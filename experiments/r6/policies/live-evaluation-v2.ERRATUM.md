# Erratum: live-evaluation-v2 (`live-evaluation-v2.sha256.json`, `96ce9f6d…`)

This was recorded on 2026-09-24, after [R6-014-BLOCK1-REVIEW.md](../reviews/2026-09-24/R6-014-BLOCK1-REVIEW.md). The lock is preserved
unchanged.

The lock's `scope` field reads "frozen after approval and before any signature". That text was carried over from version 1's tool and is
wrong for version 2.

What actually happened:
1. Version 2 was frozen after the block 1 signature (`c00247ed`) and after the collection and its first rejected audit (`6a361a3e`).
2. It was frozen after the amendment 1 approval (`382862da`), and committed (`482bc5a9`) before the amended audit of block 1
   (`db20792e`).

The lock's other contents are unaffected: the reviewed sources, import closure and records it binds, and its `approved_commit`
(`10c53c34`). Version 1's statement, which was frozen before any signature, is true of version 1.
