# S031 unsuccessful verification attempts

These logs are retained for provenance and do not establish Gate Z.

- S029-memory-limit: fresh exact-source clone at 3ead1d587f4ff5e129f73666bd466f5eac764223, no .lake before build. KRKLive.Reply was killed, Lean exit 137, lake build exit 1. Three independent clean builds were running concurrently; the 8 GiB cgroup recorded oom=1 and oom_kill=1. No proof/elaboration error was reported before the kill.
- S028-memory-pressure-stop: fresh exact-source clone at cb5d3bb713257d7cac8e3c1f9d82d8e77b746d6c, no .lake before build. The agent sent SIGTERM to its Reply compiler to release memory as the remaining two compilers approached the same limit; Lean exit 143, lake build exit 1. This is an intentional resource interruption, not a passed check.

S030 was then allowed to complete alone. New clean S028/S029 retries, run sequentially and identified separately in their pre-build logs, supply the successful evidence. No failed attempt was relabelled successful; no cached retry serves as a fresh-clone run.
