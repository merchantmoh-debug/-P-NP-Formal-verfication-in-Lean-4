## 2025-05-15 - [Lightweight Physics Simulation]
**Learning:** Simulating complex physical constants (like Spectral Gaps) for verification scripts doesn't require heavy dependencies like `numpy` or `scipy` when the goal is logic verification rather than numerical research. Using `math` and `random` reduced startup time to <0.1s.
**Action:** Prefer standard library for CI/CD verification scripts to minimize environment overhead.
