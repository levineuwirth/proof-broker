# R6-014 block 2, incident 1: an interrupted launch before any reservation

This was recorded on 2026-09-28. The resolution was approved by the operator: "Let's do it."

**Nothing was reserved, sent or spent.** The live ledger is unchanged:
- 25 rows, revision 3 (priced from capture 6);
- 11 consumed transmissions, with nothing open;
- no `bracket-l069/2` slot, and no slot directory for draw 2;
- the progress floor unchanged at 25 rows.

## What happened (times are local, +0200)

The first launch of the approved block 2 runner (revision 5, `994bf8bc`) ran in a tmux pane. The system journal excerpt is
[R6-014-BLOCK2-INCIDENT-1-JOURNAL.txt](R6-014-BLOCK2-INCIDENT-1-JOURNAL.txt):

| time | event |
|---|---|
| 22:30:47 | the pane starts the runner |
| 22:31:06 | episode `l069-draw2` begins (`episode_started`); its local `preparation-build` stage completes normally |
| 22:31:09 | the local `preparation` stage starts |
| 22:31:13 | the runner process receives an interrupt, 25.7 s after its pane started |
| 22:31:16 | a second launch starts |

At 22:31:13, the stage's outer handler (`site_stage.stage`, `except (subprocess.TimeoutExpired, KeyboardInterrupt)`) did three things:
- it SIGKILLed the stage's systemd scope ("Killed unit cgroup … with SIGKILL on client request");
- it recorded `stage_failure_recorded: supervisor_failure` with "outer watchdog interrupted the scope";
- it finalized and sealed the episode, as `episode_rejected`, `reservation_state: not_reserved`.

The pane ended at the same moment.

**Why an interrupt and not a timeout.** The stage's wall budget is 150 s, so the outer timeout (budget + 30 s) cannot fire after 4 s. No
module in the pipeline installs a signal handler, and closing a pane (SIGHUP) would have terminated Python without the handler recording
anything. The evidence is therefore a SIGINT to the runner, such as Ctrl-C in the attached pane. That is consistent with the relaunch 3 s
later, but who sent it is not established. Nothing in the pipeline raised it.

**The second launch.** It found the sealed `l069-draw2` directory. The runner's gate, the reviewed pause rule, read it (no permit, no
reconciliation) and **paused** before any launch. The run log shows only this second launch, because each launch rewrote the log file.

## Resolution

The runner has no override, so this pause is resolved by the operator's decision. The interrupted attempt is **moved out of the
collection, byte-for-byte**:
- from `cohort-live-v9/l069-draw2/`;
- to `cohort-live-v9-interrupted/l069-draw2-attempt1/`;
- 175 files, their digests identical before and after the move. The inventory is
  [R6-014-BLOCK2-INCIDENT-1-INVENTORY.txt](R6-014-BLOCK2-INCIDENT-1-INVENTORY.txt), and its own digest is `8029bab6…`.

Some records inside it name the original path. They are retained unchanged.

It is committed as retained evidence of an operational incident. It is not a slot outcome, because it reached no reservation, so the
frozen ledger and analysis have nothing to count for it. Left in the collection, it would have made the frozen auditor reject block 2:
that auditor fails closed on any outcome kind it has not reviewed, and a stop before reservation is one.

`cohort-live-v9/` again holds exactly block 1's eleven runs. A relaunch of the same runner starts `l069-draw2` fresh, since the slot was
never reserved. The pricing window is unchanged: capture 6 is admissible until 2026-09-29T20:13:37Z.

## Operating notes for the relaunch

- Do not send Ctrl-C to the pane. Detach with Ctrl-B, then d, or do not attach, and watch the log instead.
- Give each launch its own log file, so that one launch cannot overwrite another's evidence.
