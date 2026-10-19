# S023 verification environment

The official Lean 4.35.0 Linux release was downloaded and extracted outside the repository with `tar --no-same-owner --zstd`. The compiler reports commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. There are no project dependencies.

This host supplies a process ID for which `/proc/<own-pid>/exe` returns `Permission denied`, while the equivalent `/proc/self/exe` works. Lean's `lean_io_app_path` uses the former, so even `lean --version` initially failed with `failed to locate application`. This is an installation-path failure, before proof elaboration.

The accompanying [proc-path.c](proc-path.c) intercepts `readlink` solely when its argument is exactly `/proc/<getpid()>/exe`, substituting `/proc/self/exe`. All other calls are delegated unchanged. Compile it outside the source checkout with:

```sh
cc -shared -fPIC -o /tmp/s023-proc-path.so proc-path.c -ldl
export LD_PRELOAD=/tmp/s023-proc-path.so
export PATH=/tmp/lean-4.35.0-linux/bin:$PATH
```

The unmodified release Lean/Lake executables were used for the build and axiom report under this environment. The shim changes executable-path discovery; it does not replace any Lean declaration, axiom, elaborator, decision procedure or kernel check. Its source is retained so that this additional host-level dependency is explicit and reviewable. On an ordinary Linux host with accessible `/proc/<pid>/exe`, omit the shim entirely.

The proof checkout was cloned afresh from GitHub, detached at `a8bc161d2a51b92c340697af16a10e874cd9a098`, with no `formal/.lake` before the build. No Lean file was changed. Logs were written directly into the later freeze checkout, not copied from S022 evidence.
