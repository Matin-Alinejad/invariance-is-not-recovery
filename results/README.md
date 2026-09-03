# Generated results

This directory is intentionally empty in the release archive except for this file.

- Smoke checks write to `results/global_smoke/` and `results/matched_local_global_smoke/`.
- Distributed VM scripts write shard directories such as `results/primary_scaling_shard0/`.
- Merge scripts create the corresponding merged experiment directories.
- Artifact regeneration writes to `results/regenerated_artifacts/`.
- Full release reconstruction writes diagnostic and reconstructed-evidence outputs beneath `results/`.

All generated outputs are excluded from version control by `.gitignore`; the fixed reference evidence used for immediate release verification lives under `evidence/`.
