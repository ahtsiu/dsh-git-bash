import type { Context, Volatile } from "@deepseek-ai/cordis";
import {
  assertServiceableBashConfig,
  LocalBashExecutor,
} from "@deepseek-ai/dsh-bash-local";
import type { Config as LocalBashConfig } from "@deepseek-ai/dsh-bash-local";
import {
  classifyRunnerFailure,
  isRunnerSpawnFailure,
  matchesSignature,
  SandboxUnavailableError,
} from "@deepseek-ai/dsh-sandbox";
import type {
  ConfinedArgv,
  ConfinedSandboxMode,
  RunnerFailureRule,
  SandboxEnforcement,
  SandboxExecutionPolicy,
  SandboxMode,
  SandboxPolicy,
} from "@deepseek-ai/dsh-sandbox";
import type {} from "@deepseek-ai/dsh-sandbox-policy";
import type {
  ShellExecRequest,
  ShellExecSpec,
  ShellExecution,
  ShellProcess,
  ShellRunResult,
} from "@deepseek-ai/dsh-shell";
import z from "@deepseek-ai/schemastery";
import { spawnSync } from "node:child_process";
import { accessSync, constants, statSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { resolveGitBashPath } from "./discovery.js";

export { GIT_BASH_PATH_ENV, gitBashCandidates, resolveGitBashPath } from "./discovery.js";

const PACKAGE_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const GUARD_EXECUTABLE = resolve(
  PACKAGE_ROOT,
  "native",
  "bin",
  "win32-x64",
  "msys-token-guard.exe",
);
const GUARD_HOOK = resolve(
  PACKAGE_ROOT,
  "native",
  "bin",
  "win32-x64",
  "msys-token-guard-hook.dll",
);
const GIT_BASH_EXECUTABLE_PATTERN =
  /^(?:[A-Z]:[\\/]|\\\\[^\\/]+[\\/][^\\/]+[\\/]|%[^%]+%[\\/])(?:.*[\\/])?bash\.exe$/i;
const GUARD_FAILURE_RULE: RunnerFailureRule = {
  allowedExitCodes: [125],
  fatalSignatures: ["msys-token-guard:"],
};
// The guard's child-token setup fails when the restricted DACL (inherited from
// the server token's default DACL) offers no usable ordinary SID to the guard.
const SERVER_DACL_FAILURE_SIGNATURE = "openprocesstoken(child default dacl)";

// DSH derives every restricted token from the server's own process token, and
// the restricted DACL starts as a copy of the server's default DACL. Servers
// started outside MSYS2 can carry a DACL without the user SID, which blocks
// the guard's workspace-write child-token setup (exit 125). Run the guard
// helper once per server process to stamp the standard DACL shape — the same
// normalization starting `dsh web` from Git Bash gets for free.
function normalizeServerDefaultDacl(): boolean {
  if (process.platform !== "win32" || process.arch !== "x64") return false;
  let result;
  try {
    result = spawnSync(GUARD_EXECUTABLE, ["--normalize-server-dacl"], {
      timeout: 10_000,
      windowsHide: true,
    });
  } catch {
    return false;
  }
  return result.status === 0;
}

export interface Config extends LocalBashConfig {
  // Absolute Git for Windows bash.exe path. Auto-detected when blank.
  executable: Volatile<string>;
}

// 0.1.7 rejects volatile fields nested inside intersect/union. Copy the bash
// budget fields onto one object schema and add the Git Bash path beside them.
const bashConfigFields = LocalBashExecutor.Config.dict;
if (bashConfigFields === undefined) {
  throw new Error("git-bash: @deepseek-ai/dsh-bash-local Config has no object fields");
}

// Keep the path permissive enough for a legacy bad value to load. The
// settings card and `executable` getter enforce it when it is used.
export const Config = z.object({
  ...bashConfigFields,
  executable: z.string()
    .default("")
    .role("path")
    .description("Absolute path to Git for Windows bash.exe; blank uses automatic discovery.")
    .volatile(),
}) as z<Config>;

function resolveConfiguredExecutable(executable: string): string | undefined {
  const configured = executable.trim();
  if (!configured) return undefined;
  if (!GIT_BASH_EXECUTABLE_PATTERN.test(configured)) {
    throw new TypeError(
      "git-bash: executable must be an absolute Windows path ending in bash.exe",
    );
  }
  return resolveGitBashPath(configured);
}

interface ProcessFacts {
  mode: ConfinedSandboxMode;
  enforcement: SandboxEnforcement;
  denialSignatures: readonly string[];
  runnerFailureRules: readonly RunnerFailureRule[];
  runnerProgram: string | undefined;
  workdir: string;
}

function classifyDenial(result: ShellRunResult, signatures: readonly string[]): boolean {
  return matchesSignature(result.exitCode, result.stderr.text, signatures);
}

// Turn the guard's bare DACL failure line into an actionable message: the
// automatic normalization ran (or was skipped) and the server still serves
// restricted tokens without ordinary user coverage.
export function describeGuardFailure(detail: string): string {
  if (!detail.toLowerCase().includes(SERVER_DACL_FAILURE_SIGNATURE)) return detail;
  return detail + " (git-bash: the DSH server process token's default DACL lacks the user SID,"
    + " so the guard cannot prepare the restricted child token. Start `dsh web` from Git Bash"
    + " so MSYS2 restores the standard DACL shape, and see"
    + " https://github.com/inmny/dsh-git-bash/issues/4)";
}

function assertNativeGuard(mode: ConfinedSandboxMode): void {
  if (process.platform !== "win32" || process.arch !== "x64") {
    throw new SandboxUnavailableError(
      mode,
      "Git Bash restricted mode requires win32-x64, received " +
        process.platform + "-" + process.arch,
    );
  }

  for (const artifact of [GUARD_EXECUTABLE, GUARD_HOOK]) {
    try {
      if (!statSync(artifact).isFile()) throw new Error("not a file");
      accessSync(artifact, constants.R_OK);
    } catch (error) {
      throw new SandboxUnavailableError(
        mode,
        "Git Bash native guard artifact is unavailable: " + artifact + " (" + String(error) + ")",
      );
    }
  }
}

// DSH shell executor backed by Git for Windows Bash.
export class GitBashExecutor extends LocalBashExecutor {
  static inject = ["subprocess", "sandbox", "sandboxPolicy"];
  // The host projects this schema into the git-bash-shell profile entry.
  // The base static type only describes bash budgets, so the executable field
  // stays on the runtime schema while the override stays assignable.
  static override Config = Config as typeof LocalBashExecutor.Config;

  private executableCache: { configured: string; resolved: string } | undefined;
  private readonly mode: SandboxMode;
  private readonly processFacts = new Map<ShellProcess, ProcessFacts>();
  private serverDaclNormalized = false;

  constructor(ctx: Context, config: Config) {
    super(ctx, config);
    this.mode = ctx.sandboxPolicy.defaultMode;
  }

  private get gitBashConfig(): Config {
    return this.config as Config;
  }

  get executable(): string {
    const configured = this.gitBashConfig.executable.get().trim();
    if (this.executableCache?.configured === configured) {
      return this.executableCache.resolved;
    }

    const resolved = resolveConfiguredExecutable(configured) ?? resolveGitBashPath();
    this.executableCache = { configured, resolved };
    return resolved;
  }

  override get sandboxMode(): SandboxMode {
    return this.mode;
  }

  override resolve(request: ShellExecRequest): ShellExecSpec {
    const resolved = super.resolve(request);
    return {
      ...resolved,
      env: {
        ...(resolved.env ?? {}),
        // Keep Git/MSYS2 Bash in the workspace directory instead of
        // changing to $HOME on login-shell startup.
        CHERE_INVOKING: "1",
      },
      sandboxPolicy: request.sandboxPolicy ?? this.ctx.sandboxPolicy.resolve(),
    };
  }

  private argv(command: string): readonly string[] {
    return [this.executable, "--login", "-c", command];
  }

  private guardedArgv(command: string, mode: ConfinedSandboxMode): readonly string[] {
    assertNativeGuard(mode);
    return [GUARD_EXECUTABLE, "--", ...this.argv(command)];
  }

  private policy(spec: ShellExecSpec): SandboxExecutionPolicy {
    if (!spec.sandboxPolicy) {
      throw new Error("git-bash: resolved execution is missing sandbox policy");
    }
    return spec.sandboxPolicy;
  }

  private async confine(
    command: string,
    policy: SandboxPolicy,
    signal: AbortSignal,
  ): Promise<ConfinedArgv> {
    this.ensureServerDaclNormalized();
    const confined = await this.ctx.sandbox.confine(
      this.guardedArgv(command, policy.mode),
      policy,
      signal,
    );
    return {
      ...confined,
      runnerFailureRules: [...confined.runnerFailureRules, GUARD_FAILURE_RULE],
    };
  }

  private ensureServerDaclNormalized(): void {
    if (this.serverDaclNormalized) return;
    this.serverDaclNormalized = true;
    normalizeServerDefaultDacl();
  }

  override async execute(spec: ShellExecSpec): Promise<ShellExecution> {
    assertServiceableBashConfig(this.gitBashConfig);
    const policy = this.policy(spec);
    const { mode } = policy;
    if (mode === "danger-full-access") {
      return GitBashExecutor.decorateResult(
        await this.executeArgv(spec, this.argv(spec.command)),
        (result) => ({
          ...result,
          sandbox: { mode, denied: false },
        }),
      );
    }

    let confined: ConfinedArgv | undefined;
    const execution = await this.executeArgv(spec, async (signal) => {
      const prepared = await this.confine(spec.command, { ...policy, mode }, signal);
      signal.throwIfAborted();
      confined = prepared;
      return prepared.argv;
    }, (process) => {
      const facts = confined;
      if (facts === undefined) return;
      this.processFacts.set(process, {
        mode,
        enforcement: facts.enforcement,
        denialSignatures: facts.denialSignatures,
        runnerFailureRules: facts.runnerFailureRules,
        runnerProgram: facts.argv[0],
        workdir: spec.workdir,
      });
    });
    return GitBashExecutor.decorateResult(execution, (result) => {
      if (confined === undefined) {
        return { ...result, sandbox: { mode, denied: false } };
      }
      const runnerFailure = classifyRunnerFailure(
        result.exitCode,
        result.stderr.text,
        confined.runnerFailureRules,
      );
      if (runnerFailure !== undefined) {
        throw new SandboxUnavailableError(mode, describeGuardFailure(runnerFailure.detail));
      }
      return {
        ...result,
        sandbox: {
          mode,
          denied: classifyDenial(result, confined.denialSignatures),
          enforcement: confined.enforcement,
        },
      };
    }, (error) => {
      if (spec.signal?.aborted === true) spec.signal.throwIfAborted();
      if (confined !== undefined && isRunnerSpawnFailure(error, confined.argv[0], spec.workdir)) {
        throw new SandboxUnavailableError(mode, String(error));
      }
      throw error;
    });
  }

  // Decorate the handle's foreground projection in place. The handle keeps its
  // identity because per-process facts and onProcessDone key on that instance.
  private static decorateResult(
    execution: ShellExecution,
    map: (result: ShellRunResult) => ShellRunResult,
    mapError?: (error: unknown) => never,
  ): ShellExecution {
    const base = execution.result.bind(execution);
    let decorated: Promise<ShellRunResult> | undefined;
    execution.result = () => {
      decorated ??= base().then(map, mapError);
      return decorated;
    };
    return execution;
  }

  protected override onProcessDone(
    proc: ShellProcess,
    stderr: string,
    providerRejected: boolean,
    providerError?: unknown,
  ): void {
    const facts = this.processFacts.get(proc);
    if (facts !== undefined) {
      this.processFacts.delete(proc);
      const runnerFailed = providerRejected
        ? isRunnerSpawnFailure(providerError, facts.runnerProgram, facts.workdir)
        : classifyRunnerFailure(proc.exitCode, stderr, facts.runnerFailureRules) !== undefined;
      proc.sandbox = {
        mode: facts.mode,
        denied: !runnerFailed && matchesSignature(
          proc.exitCode,
          stderr,
          facts.denialSignatures,
        ),
        enforcement: facts.enforcement,
        ...(runnerFailed ? { runnerFailed } : {}),
      };
    }
    super.onProcessDone(proc, stderr, providerRejected, providerError);
  }
}

export default GitBashExecutor;
