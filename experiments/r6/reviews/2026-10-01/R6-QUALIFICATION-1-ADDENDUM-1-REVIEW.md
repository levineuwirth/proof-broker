# R6 qualification 1, addendum 1 — review

Supplied by the reviewer in session on 2026-10-01, against addendum 1 as committed at `5fd27955`. It is recorded verbatim below.

---

 The central result checks out: 24 certificate alone, 7 sufficient with context referenced, 1 not established, and 16 unbound. Both targets agree throughout. The qualification lock and live-evaluation lock verify, and the controls
  match the locked tool and sources.

  One factual correction in the addendum’s consistency paragraph (experiments/r6/R6-QUALIFICATION-1-ADDENDUM-1.md:30): the declaration counts vary by export. For example, l096/l099 have 1,336 identical, 178 annotation-only, and 45
  replayed, rather than 1,923/218/1,798.

  Suggested replacement:

  > Every export’s shared constants matched Init up to annotations. The remaining declarations were kernel-checked through addDecl on 4.32.2; counts vary by export and are retained in the audit record.

  This does not change the classifications. Keeping the 16 unbound slots outside the claimed results and treating l070 draw 5 as requiring diagnosis are appropriate.

  I changed nothing and did not rerun the proof audit.
