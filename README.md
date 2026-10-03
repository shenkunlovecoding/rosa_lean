# Lean formalization of the run-compressed ROSA notes

Machine-checked Lean 4 (4.33.1, `import Std`, **no Mathlib**) formalization of
`ROSA_run_compressed_formalization_notes_2026-09-12.md`.

For a derivation-grade companion that follows the narrative from the original
ROSA definition through the compression chain, Lean theorem map, current
Complexity ledger, and future directions, see [`ALGORITHM.md`](ALGORITHM.md).

## Build / reproduce

This is a **Lake** project (`lakefile.lean`, `lean-toolchain = v4.33.1`), so
there is no manual `lean -o` glue.  It is **Std-only** — a package with zero
external dependencies, so `lake build` is seconds, not hours.

```sh
cd task3/lean_formalization
lake build                 # builds the whole `LeanFormalization` lib (~0.5 s warm)
./build.sh                 # same, plus prints ALL_LEAN_OK
```

* All 59 source modules (`Route`, `CutArith`, …, `Check`) are declared as `roots` of the
  `LeanFormalization` library; artifacts go to `.lake/build/` (git-ignored).
* `lake build` type-checks everything and prints the `#check` lines when
  `Check.lean` is (re)compiled; to re-print them explicitly:

  ```sh
  lake env lean Check.lean     # re-runs every headline `#check`
  ```

Every theorem below is **fully proved** (no `sorry`, no extra axioms); the
build fails otherwise.

## Files

| File | Contents |
|---|---|
| `Route.lean` | `Route = (len, endpoint)`; ROSA priority `rle`, `rmax`, `rmaxList` + lub/validity lemmas (notes §16.1/§16.2). |
| `CutArith.lean` | Normalizing constructor `mk`; per-endpoint K-cut `kcutCand`; brute K-cut; `hook_split` (§4.2). |
| `HookCut.lean` | §4.3 **Hook-Envelope Theorem**. |
| `QCut.lean` | §5 **Bulk Q-Cut**. |
| `Lcs.lean` | §1.2 LCSuffix: `SuffixEq`, `maxSuffix`, `lcsLen` and its greatest-length characterization. |
| `RunRectangle.lean` | §6.3 **Run-Rectangle LCS Theorem** (all four branches) + §7 RSP row shape. |
| `Capacity.lean` | §7.1 run capacity: `run_capacity_reaches` + `run_capacity_latest_endpoint` (three-way latest endpoint). |
| `Repair.lean` | §9.3 **Repair Boundary-Support** (L/R) + strict-interior triviality; §9.5 left-edge RSP. |
| `RunRectangleLcp.lean` | forward (LCP) Run-Rectangle (§9.5 right edge): `lcp_rectangle_*` + `repair_edge_right_rsp`. |
| `RunHookSummary.lean` | §8 run-compressed K-Hook summaries (Phase E): `RspRow`, δ shape, `P_run_eq` / `U_plateau_max` / `A_run_eq`. |
| `AffineEnvelope.lean` | §11 Phase H core: affine Route + pairwise winner-convexity + finite-template envelope (**no ROSA/string dependency**). |
| `OwnerEnvelope.lean` | §11 Phase H step 2/3: finite-template owner envelope (`envWins_interval`), `A`/`P`/`U` gluing, and the §9.4 interior-bulk bridge reduction. |
| `KDeleteROSA.lean` / `KDeleteEquivalence.lean` | ROSA deletion candidates over the exact endpoint domain `e < t`; the latter proves `rosaKDelete.best = bruteKCut` unconditionally. |
| `CreditRepairReduce.lean` | `ROSA_Credit_New_Results` §1: the strict-interior Q-owner keeps **two** repair candidates (`ctxBridge`, `carry_forces_k_right_end`, `qOwnerBridges_carry_unique`, `two_candidates_reproduce_envelope`). |
| `CreditCandidateCount.lean` | §2: candidate count `C ≤ T(5·R_Q+4·R_K)` (`repair_candidate_bound`), run-cover bounds (`sum_len_le_of_ordered`, `sum_interior_le_of_ordered`), and §1 as "≤ 2 per strict-interior Q-owner" (`strictInterior_keep_le_two`). |
| `CreditQEExpiry.lean` | §3: the Q repair envelope is *priority sort + expiry record* (`bridge_rle_const`, `scanAll_covered`, `scanAll_length_le`, `qExpirySkyline_spec`). |
| `CreditBlockConv.lean` | §4: shifted-dot block convolution identity (`convCoeff_eq_blockDot`), full-block decomposition (`blockDecomposition`), D-channel lift, block count, and the optimal-`B` arithmetic (`balance_div`). |
| `CreditCRT.lean` | §5: CRT recovery is unique once the modulus product exceeds `2·H_g` (`crt_unique`, `crt_unique_three`). |
| `Check.lean` | `#check` of every headline theorem. |
| `lakefile.lean` / `lean-toolchain` | Lake project (lib `LeanFormalization`, Std-only, Lean 4.33.1). |

## Mapping to the notes' §15 "11 priority theorems"

| # | notes' name | Lean theorem | status |
|---|---|---|---|
| 1 | `kcut_single_endpoint` | `CutArith.hook_split` (+ `kcutCand`) | ✅ |
| 2 | `kcut_hook_decomposition` | `HookCut.kcut_hook_decomposition` | ✅ |
| 3 | `qcut_length_and_latest_endpoint` | `QCut.qcut_length_and_latest_endpoint` | ✅ |
| 4 | `run_rectangle_lcs` | `RunRect.run_rectangle_symbol_ne` / `_offset_lt` / `_offset_gt` / `_offset_eq` | ✅ |
| 5 | `run_grid_gamma_recurrence` | `RunRect.run_grid_gamma_recurrence` | ✅ |
| 6 | `run_capacity_latest_endpoint` | `Capacity.run_capacity_latest_endpoint` (+ `run_capacity_reaches`, `RunRect.run_rectangle_rsp`) | ✅ |
| 7 | `repair_left_boundary_support` | `Repair.repair_left_boundary_support` | ✅ |
| 8 | `repair_right_boundary_support` | `Repair.repair_right_boundary_support` | ✅ |
| 9 | `repair_strict_interior_trivial` | `Repair.repair_strict_interior_trivial` | ✅ |
| 10 | `repair_edge_left_rsp` | `Repair.repair_edge_left_rsp` | ✅ |
| 11 | `repair_edge_right_rsp` | `RunRectLcp.repair_edge_right_rsp` | ✅ |

**All 11 headline theorems are machine-checked** — but for items 4/5/6 the
theorems carry non-degeneracy hypotheses (`2 ≤ x`, `c+x ≤ d`, `0 < ap`, `0 < cp`),
so this is the *main (non-degenerate) case*, not an all-cases closure.  See
"Corrections from review" below.

## Headline statements (verbatim signatures)

* `kcut_hook_decomposition : bruteKCut ell t s = hookCut ell t s`, where
  `hookCut = rmax A (rmax P R)` — i.e. `KCut(t,s) = max{A(s),P(s),R(s)}`.
* `qcut_length_and_latest_endpoint : bruteQCut ell t u = qcutClosed ell t u`
  — closed form `mk (min L_base (t-u)) (latest endpoint ≥ λ)`.
* `run_rectangle_*`: for maximal constant runs `Q=[a,b]` (`αs`) and `K=[c,d]`
  (`βs`) and `t∈[a,b]`, `e∈[c,d]`:
  * `αs ≠ βs` → `lcsLen = 0`
  * `αs = βs`, `x < y` → `lcsLen = x`   (`x = t-a+1`, `y = e-c+1`)
  * `αs = βs`, `y < x` → `lcsLen = y`
  * `αs = βs`, `x = y` → `lcsLen = x + lcsLen q k (a-1) (c-1)`  (needs `a,c > 0`)
* `repair_left_boundary_support` : `0 < lcsLen q k (p-1) (u-1) → p = a ∨ u = c`.
* `repair_right_boundary_support`: `0 < lcpLen q k Tq Tk p u → p = b ∨ u = d`.
* `repair_strict_interior_trivial` : strict interior ⟹ `L = R = 0`.
* `repair_edge_left_rsp` : left-edge context `lcsLen q k bp (u-1)` is ramp / spike
  / plateau in `u` (Run-Rectangle RSP against the previous Q run).

## Phase E — run-compressed K-Hook summaries (§8) — *non-degenerate core*

The fixed row `ell` restricted to a `α=β` K run gets the abstract shape

```lean
structure RspRow (ell : Nat → Nat) (c d x γ : Nat) : Prop where
  ramp    : e-c+1 < x → ell e = e-c+1
  spike   : e-c+1 = x → ell e = x+γ
  plateau : x < e-c+1 → ell e = x
```

plus `rspRow_of_rectangle` (a real ROSA row satisfies it, from `run_rectangle_rsp`).
On top of it:

* **δ shape (§8.1):** `delta_ramp` (`δ = c-1`, constant), `delta_spike`
  (`δ = c-1-γ`), `delta_plateau` (`δ = e-x`, unit slope) — the boxed
  "constant-δ ramp + one spike + unit-slope plateau".
* **E1 `P_run_eq`:** the brute `max_{δ>s}` route over the run equals the max of
  the three records `rampRec` / `spikeRec` / `platRec` (ramp-last, spike,
  plateau-last).
* **E2 `U_plateau_max`** (+ `plateau_dl_le_iff`, `plateau_e_eq_delta`): on the
  plateau `e = δ+x`, so the endpoints reaching `δ ≤ s` are exactly `e ≤ s+x`,
  with latest endpoint `min d (s+x)`.
* **E3 `A_run_eq`:** the per-run prefix winner is `aComp` = max(last endpoint,
  spike) — the "current-run local prefix winner + global carry".

All under the normalisation `2 ≤ x`, `c+x ≤ d` (so ramp, spike and plateau are
all non-empty); the degenerate run lengths are the analogous finite edge cases.

## Phase H — affine Route envelopes (§11, ROSA-independent core)

Following the "change of proof posture" strategy: **do not** attack
`OwnerEnvelope = O(1) pieces` directly.  First the abstract, string-free fact.

```lean
structure AffRoute where
  aL bL aE bE : Int          -- len = aL*t+bL, endpoint = aE*t+bE,  t : Int
def wins (f g : AffRoute) (t : Int) : Prop :=   -- ROSA lex priority
  f.len t > g.len t ∨ (f.len t = g.len t ∧ f.ep t ≥ g.ep t)
```

* `affine_wins_convex` (pure `Int` arithmetic): the RO SA winner set
  `{t : f.wins g t}` is **convex** (an interval).  Reason: the length difference
  `Δ_L` is 1-D affine so its sign changes at most once; only `Δ_L = 0` reaches
  the affine endpoint tie-break `Δ_E`; hence at most a constant number of
  breakpoints.
* `AffRoute.wins_convex` / `wins_interval`: the same, phrased on an integer
  interval `[lo,hi]`.
* `AffRoute.wins_list_convex`: **finite candidate templates ⇒ `O(1)` envelope** —
  for any finite list `L` of affine routes, `{t : ∀ g∈L, f.wins g t}` is an
  intersection of intervals, hence an interval (one piece per candidate).
* Templates `tmplConst` / `tmplSlopeUp` / `tmplPlateau` / `tmplRamp` cover the
  shapes that occur inside one one-bit run pair (`constant`, `slope ±1`, `RSP`,
  `single spike`, `bounded affine segment`).

So `finite candidate templates + pairwise affine envelope lemma ⇒ O(1) owner
envelope`, without Lean ever needing the ROSA string semantics.

### Step 2 — finite-template owner envelope (`OwnerEnvelope.lean`)

* `envWins f cs t := ∀ g ∈ cs, f.wins g t` — the candidate list `cs` is the finite
  template set.
* `envWins_interval`: the owner winner set is an interval ⇒ at most one piece per
  template.  `two_winner_interval`: two routes switch winner at most once.
* Template library for the run-pair shapes: `bridgeRoute` (§9.1 bridge:
  `ℓ=L+1+(t-p)`, `r=u+(t-p)`), `spikeRoute`, `rampRoute`, `plateauRoute`,
  `rspTemplates` (the §9.5 ramp+spike+plateau edge).
* ROSA side, `interior_bridge_value`: §9.4 — a strict-interior centre has
  `L=R=0`, so its bridge is a single constant template `(1,u)`; the `Θ(mn)`
  interior centres collapse and no string semantics is needed downstream.

### Step 1 (ROSA side) — run-pair template enumeration + counts

* `centers` / `runPairCands`: the causal one-bit centres `(p,u)` of a run pair,
  one `AffRoute` bridge route each (§9.1); `runPairCands_interval` — the owner
  envelope over them is an interval.
* `runPairTemplates` (§9.4 interior bulk + §9.5 four edges + four corners) and
  `runPairTemplates_length ≤ 9`: **`O(1)` templates per run pair**.
* `interior_same_birth`: all strict-interior centres share the birth value
  `(1,u)` (the `Θ(mn)` interior bulk collapses to one template).
* `row_interval`: gluing `R_K` run pairs (`List.flatten`) keeps the interval
  winner set ⇒ **`O(R_K)` pieces** over the whole row.

### Step 3 — global multi-run gluing

The three directions are all list concatenation of candidate lists, so the
global envelope is again an interval:

* `envWins_append` / `glue_A_leftToRight` — `A`: left-to-right carry.
* `glue_P_threshold` — `P`: threshold records suffix-max (`filter` commutes with
  `++`).
* `glue_U_union` — `U`: plateau-interval union + prefix-max.
* `glue_interval` — corollary: whole-row owner envelope is `O(#templates)` pieces.

## Phase H (new) — `Bridge` semantics chain (§3–§6 of the next-stage guide)

The next-stage guide replaces the old `AffRoute`/`envWins` approach with a real
`Bridge` semantics layer.  Steps 1–3 are machine-checked (new files):

* **step 1 `RosBridge.lean`** — `Bridge` (`p,u,L,R`), `birth`/`death`/`Active`
  (`[p, p+R]`), `routeAt`, normalised priority `kappa = (p-L, -(u-p+1))`;
  `bridge_kappa_const : routeKappa t (routeAt t) = kappa` (κ is constant along
  the lifetime) and `route_better_iff_kappa` (ROSA route priority ↔ κ, reversed).
* **step 2 `QBridge.lean`** — `q_bridge_beats_cut`: an active bridge born at the
  Q-owner `p` strictly beats the Q-cut baseline (whose length is capped at `t-p`,
  `QCut.bruteQCut_len_le`).  So Q-side repair drops the cut baseline entirely.
* **step 3 `CommonBirth.lean`** — `common_birth_winner_iff`: with a common birth
  `p` and only expiries, `b` wins exactly on `[max(p, M_b+1), e_b]` (`M_b` = the
  largest expiry among strictly-better candidates) — the abstract Q-suffix
  theorem `I_Q(b)`.
* **step 4 `Interior.lean`** — strict-interior bulk compression.
  `interior_bridge_route`: an interior bridge is active only at `t = p` with
  value `(1,u)` (from `repair_strict_interior_trivial`, `L=R=0`).
  `k_interior_bulk_equiv` (§8): for a fixed K-owner `u` the interior births
  `t = p` range exactly over `[max(a+1,u+1), b-1]` — one constant-route segment.
  `q_interior_bulk_max` / `q_interior_bulk_attained` (§7): for a fixed Q-owner
  `p` the interior endpoints are capped by `u_* = min(d-1, p-1)`.
* **step 5 `RspSummary.lean`** — cut-independent generic `RspShape`
  (ramp / one spike / plateau) with `value`, `ramp_mono` and `le` (the three
  records cover the whole range); `left_edge_context_rsp` instantiates it from
  the §9.5 left-edge context `u ↦ L(a,u)`.  Phase E's `RspRow` is the same shape
  on the K-endpoint axis, so cut and repair edges share one summary.
* **step 6/7 `KDeleteAbstract.lean`** — the abstract `𝒟ᵤ`: `KDeleteFamily`,
  `best`, `trim`, and **only two structural properties** (`HasPrebirthShadow D c`
  and `TrimClosed D`, predicates — not axioms).  Derived from them:
  `trim_kappa` (pure arithmetic, trim preserves `κ`), `kdelete_step`,
  `beats_delete_monotone` (beats-delete monotonicity, *derived* not assumed),
  `shadow_not_beats`, `better_future_bridge_blocks_before_birth`.
* **step 8 `KSkyline.lean`** — `k_suffix_winner_iff`: assembling shadow +
  trim-closure + the deletion threshold `d`, `b` is the K-side winner exactly on
  `[max(p, d, M+1), e_b]`.  No `q`/`k`/`lcsLen`/`SuffixEq` anywhere.
* **step 8 (parametric) `KSuffix.lean`** — the bare ceiling `k_suffix_ceiling`
  (guide §14).
* **(2) ROSA semantic discharge `KDeleteROSA.lean`** — `rosaKDelete q k u` is the
  concrete `𝒟ᵤ` ("delete `k[u]`": the suffix-match routes of `q[0..t]` whose
  matched `k`-range avoids `u`), with endpoint domain `e < t` exactly as in
  `LCSuffix(e<t)` and `bruteKCut`.  From it, **derived** (not assumed):
  `rosa_trim_closed : TrimClosed (rosaKDelete q k u)` and
  `rosa_has_prebirth_shadow : RealisedK → HasPrebirthShadow (rosaKDelete q k u) c`
  (the witness is the left-context route and its trims, all carrying `κ_c`).
  Capstone `rosa_k_suffix_winner_iff`: the step-8 K-suffix with both abstract
  predicates **discharged from the string layer**.  `KDeleteEquivalence.lean`
  further proves the unconditional identity
  `(rosaKDelete q k s).best t = bruteKCut (lcsRow q k t) t s`.
* **step 9 `OwnerBridges.lean`** — fixed-owner *actual* bridge collections.
  `mkBridge`, `Centre` (positional causal-centre condition), `qOwnerBridges`
  (fixed Q-owner `p`) / `kOwnerBridges` (fixed K-owner `u`) with `mem_*`
  characterisations; the owner/bit/run-pair conditions are packaged as
  `Query` with `Query.bridges` / `mem_Query_bridges`.  `qOwnerBridges_birth`
  records the **common birth** fact step 10 needs.  The bit label `j` is
  bookkeeping only — the algebra needs just `αs ≠ βs` (one-bit adjacency).
* **step 10 `OwnerCompress.lean`** — fixed-owner *compressed* candidates.
  A general `Cand {lo hi : Nat; rt : Nat → Route}` (needed because the K-side
  strict-interior bulk is a constant route on a whole segment, not a bridge),
  `candOf : Bridge → Cand`, the field `field cs t` (best active route), and the
  compressed collections:
  * `qOwnerCompressed` — the strict-interior K-centres collapse to the single
    best endpoint `u_* = min(d-1, p-1)` (§7); K-edge centres stay.
  * `kOwnerCompressed` — the strict-interior Q-centres become the one
    constant-route candidate `kInteriorBulk` on `[max(a+1,u+1), b-1]` (§8); Q-edge
    centres stay.
  * **step 11-Q `OwnerCorrect.lean`** — `qOwnerCompressed_field`:
    `field (qOwnerCompressed …) t = field (Actual) t` for **all** `t`, i.e. the
    Q-side compression is *exact*.  Machinery: `field_candsOf` (`field` of a
    bridge list = `fieldBridges`), the generic "dropping dominated members
    preserves the field" lemma `fieldBridges_filter_eq`, and the key domination
    `qOwner_dominated` (a dropped strict-interior centre is dominated at every
    `t` by the kept `u_*`, via `mkBridge_strict_interior` = `L=R=0`, active only
    at `p`, value `(1,u)`).
  * **step 11-K `OwnerCorrectK.lean`** — `kOwnerCompressed_field`:
    `field (kOwnerCompressed …) t = field (Actual) t` for **all** `t`, i.e. the
    K-side compression is *exact*.  The strict-interior Q-centres are replaced by
    `kInteriorBulk`; machinery: `field_kInteriorBulk` (a single candidate acts as
    `bulkRoute`), `bval_dropped` (a dropped bridge is active only at `p`, value
    `(1,u)`), `bval_le_bulkRoute` (domination) and `bulkRoute_le_field`
    (the witness `mkBridge … t u`).  Reuses `OwnerCorrect`'s generic lemmas.
  * **§11.1 (part 1) `WinnerPieces.lean`** — the **§20 exact candidate bound**:
    `qOwnerCompressed_length_le_three` / `kOwnerCompressed_length_le_three`
    (strict-interior owner ⇒ the compressed list has `≤ 3` elements: the interior
    bulk + the two run-edge centres).  Uses `List.Nodup.length_le_of_subset`
    (Std) + `Nodup` of the source collections.  Explicit constant, no Big-O.
    Also **§11.1 (Q side)**: `qOwner_field_three` — the Q-side winner route is
    *exactly* the max of the three explicit **slot** contributions `c`, `d`,
    `u_* = min(d-1, p-1)` (`qSlot`, `unmatched` when the slot is not a live kept
    centre) ⇒ **`O(1)` winner pieces**, via `qOwner_filter_subset`
    (`live kept centres ⊆ {c, d, u_*}`).  K side: `kOwner_field_three` — the winner
    is *exactly* the max of the three K-side slots (bulk + `a` + `b`), via
    `kEdge_rmax_eq` (`live kept centres ⊆ {a, b}`).
* **step 12a `Gluing.lean`** — multi-run **semantic** gluing.  The field of a
  concatenation is the `rmax` of the fields (`field_append`, `fieldBridges_append`
  from `Route.rmaxList_append`), hence `field_flatten` /
  `fieldBridges_flatten`: the multi-run IR is the fold `rmaxList` of the
  per-block fields.  `glue_two` / `glue_pairs` glue per-block compressions into
  the multi-run equality.  **No `O(R_K)` claim** (that is 12b).
* **step 12b `Phase12b.lean`** — size / piece-count, following the 12b guide:
  * **§20/§13 candidate bound** — `flatten_length_le`: a multi-run IR of blocks
    each `≤ 3` candidates has `≤ 3m` candidates.
  * **§2/§3 no-re-entry pigeonhole** — `compress` (collapse adjacent
    duplicates = maximal constant segments), `NoReentry l := (compress l).Nodup`,
    and `segments_le_of_subset`: a no-re-entry sequence has at most as many
    maximal segments as any list containing all its labels.
  * **§13 combined** — `segments_le_three_mul`: `≤ 3m` winner segments
    **given** no-re-entry.  Exact bound, no Big-O.
  * **§2 closing step** — `IsInterval` (order-convex winner set), `IsSegStart`,
    `segStart_label_ne` (*interval ⇒ distinct segment starts carry distinct
    labels*, i.e. canonical-identity no re-entry), and
    **`segments_le_three_mul_of_isInterval`**: `≤ 3m` winner segments given
    (i) blocks `≤ 3`, (ii) every winner-label's preimage an interval,
    (iii) winners drawn from the blocks.  **Fully closed.**
  * **§1/§2 one bridge = one affine piece** — `routeOfKappa κ t = (t-κ.1+1, t-κ.2-1)`;
    **`bridge_route_eq_routeOfKappa`** (`bridge_route_affine`): *every* repair
    bridge is exactly the slope-`(1,1)` line of its `κ`, so `bridge_affineOn`
    gives **one affine piece per winning interval** — regardless of how many
    distinct Route *values* occur inside it.  `routeOfKappa_inj`: `κ` determines
    the line, so distinct `κ` are distinct pieces.  (Route-value no-re-entry is
    **irrelevant** and false: one bridge living `T` steps already yields `T`
    values.)
  * **§13 overlay bound (generic, ROSA-free)** — `overlay_breakpoints_le`:
    base with `q` breakpoints overlaid by `r` intervals has `≤ q + 2r` (one base
    piece splits into at most three).  Tight in the abstract; storing the overlay
    *un-materialised* costs only `q + r`.
  * **Discharged for ROSA** — `qCBCand_isInterval` (via
    `common_birth_winner_iff`) and `kSuffixWinner_isInterval` (via
    `KSkyline.k_suffix_winner_iff`, i.e. the **deletion-baseline-aware** K winner
    the brute force demands).
  * **Open (the one remaining ROSA obligation)**: `BlockWinnerNoReentry`.
    **Not** implied by the block-local §11.1 theorems (guide §5).  A brute-force
    search (`research/research_rosa/bruteforce_12b.py`, 117376 cases) pins down its exact
    form: (i) it must be stated over the **canonical winner identity**, not the
    raw route value (the Q side already fails value-level no-re-entry); (ii) the
    **K side fails without the deletion baseline** (`q=000110, k=010100`, owner
    `u=2`, ids `(3,2)(4,2)(3,2)`) — so it must go over `rosaKDelete`, matching
    `k_suffix_winner_iff`; (iii) the Q side *does* hold (0 violations), matching
    `common_birth_winner_iff`.
  Interface: `mem_qOwnerCompressed`, `mem_kOwnerCompressed_iff`,
  `kInteriorBulk_mem`, `candOf_active`, `kInteriorBulk_rt`.

**Status after the 2026-09-18 child-agent expansion:** the old step 6–12 gaps
are now largely closed by dedicated modules: `KDeleteROSA`/`KDeleteEquivalence`
discharge the deletion baseline and prove the unconditional K-delete = Hook
equivalence; `OwnerBridges`/`OwnerCorrect`/`OwnerCorrectK`/`OwnerTemplateEquivalence`
give fixed-owner exact compression; `Gluing`/`Phase12b`/`AffineLifetime`/
`EnvelopeEssentialEvents`/`EnvelopeExecutable` give lifetime-aware winner
intervals and an executable event scan.  The remaining no-re-entry statement is
not an unconditional global one: `BlockWinnerNoReentry.crossBlock_canonical_reentry`
exhibits re-entry across competing owner blocks.  The correct global statement
therefore carries an explicit `CrossBlockIdentityIntervals`/coverage condition,
while fixed-owner Q/K results are proved directly.

## Theory status & what it buys for a kernel (2026-09-12)

**Closed in Lean** (59 source modules, `0 sorry`): steps 1–11 (run-compressed exact
representations; Hook Q/K cut; Run-Rectangle LCS; Boundary-Support; capacity
records; the bridge layer; fixed-owner compression **exact** on both sides),
§11.1 (`O(1)` winner pieces per owner), 12a (multi-run **semantic** gluing),
12b (canonical-identity `#segments ≤ 3m`; **one bridge = one affine piece** via
`routeOfKappa`, slope `(1,1)`; generic overlay bound `q + 2r`), plus the
2026-09-18 closure modules: dense and run-compressed Hook scans, full boundary
partition/zero/certificate extraction, optional boundary windows, capacity
argmax and automatic run cover, lifetime essential events and executable scan,
fixed-owner M3 cut+repair envelopes, unified initial-run gamma recurrence, and
exact/abstract-error payload contraction.

**Residual conditions / explicit non-claims:**
* *Cross-owner winner identities* can re-enter; `BlockWinnerNoReentry` proves a
  concrete counterexample.  Global segment bounds require explicit
  `CrossBlockIdentityIntervals` and active coverage; fixed-owner Q/K theorems do
  not depend on that global premise.
* *K-window extraction* is reduced to `DeletionWindowAnchor` by
  `OwnerKWindowDischarge`; construction of that anchor from arbitrary runtime
  data is an extraction obligation, not an unproved algebraic lemma.
* *Runtime/Triton refinement* is not formalized.  The Lean layer proves the
  discrete and exact-integer algebra; it does not prove the CUDA/Triton kernel
  implements the same operations.
* *Float32/Float64 semantics* are not bound.  `PayloadErrorBound` proves an
  abstract propagation bound and degenerates to the exact integer theorem at
  zero rounding budget; IEEE rounding, FMA, NaN, overflow, and reduction order
  remain runtime/numerical obligations.
* *Worst-case near-linearity* is not claimed; the cut-side parameter remains a
  parameter, as stated below.

**Blocked — the spec admits it (§7.4):** the baseline/cut side has **no**
near-linear bound (`O(R_Q R_K + T R_K log R_K)`, degrading to `O(T² log T)` when
`R_K = T`; explicitly *"not a worst-case near-linear theorem"*).  Hence `q` in
`Pieces^final_K ≤ q + 6m` is a **parameter, not a bound**.

**What the theory buys (repair side):** per owner `≤ 3` compressed candidates
(§20); the route is **just `κ`** (2 × int32 — no route table, via
`bridge_route_eq_routeOfKappa`); the winner has `≤ 3m` segments; the IR is stored
as *base (q pieces) + overlays (r intervals)* ⇒ `q + r`, **not** `q + 2r`
(`overlay_breakpoints_le`); Boundary-Support ⇒ non-trivial `(L,R)` lives only on
the run-rectangle boundary, so **no `O(|Q_i|·|K_j|)` materialisation**.

**Empirical backing (measured, packed — `research/research_rosa/measure_packed_runs.py`):**
the packing is now known from `references/RWKV-v8/260222_rosa4bitLM_L12.py`: **4 adjacent
channels form one little-endian 4-bit symbol** (`qsym[t] |= bit(ch) << bb`,
`ch = 4g+bb`, ROSA uses sign bits).  Re-measuring `task3/artifacts/model_bits.pt` with that
packing (bit-level results reproduce spec §13.1/§13.3 **exactly**, validating the
pipeline):

| L | bit `R_Q` | bit `R_K` | sym `R_Q` | sym `R_K` | sym `R_Q·R_K` | median | `A₁` | /`T²` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| L1 | 236.5 | 228.2 | 462.8 | 453.5 | 210,336 | 218,088 | 57,022 | 0.80 |
| L4 | 53.4 | 34.3 | 164.2 | 112.4 | 24,469 | 9,635 | 8,434 | 0.093 |
| L8 | 23.3 | 8.6 | 85.5 | 30.6 | 4,242 | 144 | 1,902 | 0.016 |
| L11 | 22.1 | 6.3 | 81.8 | 21.4 | 1,728 | 89 | 646 | 0.0066 |
| L12 | 19.9 | 6.9 | 72.9 | 23.4 | 2,450 | 49 | 439 | 0.0094 |

So **under the real packing the run structure survives** on deep layers
(`R_Q·R_K` ≈ 10³ vs `T² = 262144`, `A₁` in the hundreds), i.e. the cost
`O(R_Q R_K + T R_K log R_K)` is still `O(T)` there — near-linear, though the
constant is worse than per-bit (packing roughly ×7 on `R_Q·R_K`).  L1 (46% flip)
remains a concrete non-example.  Caveats: single capture (4×512 rows);
`A₁` counted undirected, so the causal half-plane (§11.1) roughly halves it.

**Explicit non-claims:** this is **not** an *unconditional* near-linear guarantee
(the cut side is the bottleneck, and near-linearity is a function of the *input's*
run sparsity, not a theorem).  `PayloadContraction`/`PayloadRouteAdapter` prove
the integer-exact M4 contraction algebra, and `PayloadErrorBound` gives an
abstract error propagation model; none of them binds IEEE `Float32`/`Float64`
addition, multiplication, FMA, reduction order, NaN, or overflow semantics.
The forward pass and surrogate gradients remain out of scope.

## Corrections from the 2026-09-12 review

| # | issue | status |
|---|---|---|
| 1 | `QCut` for `u > t`: cap `t-u` went negative ⇒ every candidate collapsed to `unmatched` (should be the base route).  Kernel-verified but specification bug. | **fixed**: `qcutCand`/`qcutLambda` now branch on `t < u`; `qcut_future : t < u → bruteQCut = qcutClosed` (both = base); `qcut_length_and_latest_endpoint` now takes `hu : u ≤ t`. |
| 2 | Left context `lcsLen q k (p-1) (u-1)` underflows at `u = 0` (or `p = 0`), silently comparing `k 0`. | **fixed**: added `Repair.leftCtx` / `rightCtx` with the `p=0 ∨ u=0 → 0` guard; `OwnerEnv.runPairCands` now uses `leftCtx`. |
| 3 | `AffRoute` has no active interval, so `wins_list_convex`/`envWins_interval`/`row_interval` only hold for the "all candidates forever" model; real bridges have lifetimes and the winner set need not be an interval. | **fixed at fixed-owner level**: `AffineLifetime` models birth/death and re-entry, `EnvelopeEssentialEvents` supplies a finite deduplicated event set, and `EnvelopeExecutable` proves an ordered-event scan exact. Unconditional cross-owner no-reentry remains false/conditional as documented. |
| 4 | `runPairCands` mixed candidates of different owners, which never compete in real ROSA backward. | **fixed**: split into `qOwnerCands` (fixed Q-owner `p`) and `kOwnerCands` (fixed K-owner `u`), each with its interval theorem. |
| 5 | `runPairTemplates` is "9 arbitrary `AffRoute` packed into a list" with no equivalence to real bridges. | **fixed by corrected IR**: `OwnerTemplateEquivalence.runPairTemplates_corrected_max_eq_actual` proves the corrected fixed-owner template field equals the actual bridge field; `EffectiveOwnerM3` connects it to cut+repair semantics. |
| 6 | `run_grid_gamma_recurrence` needs `0 < ap`, `0 < cp`, so the first row/column (base case) is uncovered. | **fixed/unified**: `RunRectangleInitial.run_grid_gamma_recurrence_leftCtx` covers the initial-row/column cases using `Repair.leftCtx`. |
| 7 | `run_capacity_latest_endpoint`'s name is stronger than its statement (it is the "core lemma implying the classification", not an explicit `argmax`). | **fixed**: `CapacityComplete.run_capacity_maxEndpoint?_correct` gives the explicit argmax/none classification; `CapacityMultiRun`/`CapacityConcrete` add multi-run aggregation and concrete run coverage. |
| — | Phase E summaries carry `2 ≤ x`, `c+x ≤ d` (non-degenerate only: `x=1`, spike out of range, empty plateau, short/initial runs uncovered). | **fixed**: `HookDegenerate` and `RunHookCompressedScan` close the degenerate P/U/A cases and connect dense scans to run-compressed summaries. |

Accepted as genuinely closed: `Route` (priority), `Lcs` (`SuffixEq`/`lcsLen`),
`HookCut` (Hook decomposition), `HookScan`/`RunHookCoverage`,
`RunRectangle` and `RunRectangleInitial`, `Repair` Boundary-Support,
`BoundaryPartition`/`BoundaryZeroCertificates`/`BoundaryCertificates`/
`BoundaryRangeCount`/`BoundaryOptionalWindow`, and the capacity closure modules.

## Honest boundaries

* **Phase H is now closed at fixed-owner level, but not as an unconditional
  cross-owner statement.**  `AffineLifetime` explicitly models birth/death and
  proves re-entry is possible; `EnvelopeEssentialEvents` gives a deduplicated
  finite event set and `EnvelopeExecutable` proves the scan exact on ordered
  events.  `OwnerTemplateEquivalence` and `EffectiveOwnerM3` prove fixed-owner
  raw/effective envelopes, while `OwnerKWindowDischarge` reduces K-window
  assumptions to an explicit deletion-window anchor.  `BlockWinnerNoReentry`
  proves that cross-block canonical identities can re-enter, so any global
  `≤3m` result must carry explicit `CrossBlockIdentityIntervals` and active
  coverage assumptions.
* **item 5** (`RunRect.run_grid_gamma_recurrence`) is a direct corollary of
  `run_rectangle_symbol_ne`/`_rsp` instantiated at the predecessor run pair
  `(Q_{i-1}, K_{j-1}) = ([ap,bp],[cp,dp])`; `RunRectangleInitial` removes the
  remaining initial-row/column positivity hypotheses.
* All statements are the **pure arithmetic/string** layer; the `δ : Int`
  (-1 handling), zero-length→`(0,-1)` normalization, and `u < p` causal
  separation flagged in notes §16 are respected (`Route.Valid`, `mk`).

## Gotchas found while formalizing (feedback for the notes)

* `lcsLen` is defined by a bounded `maxSuffix` fold, not by `Nat.find`; the
  useful interface is `lcsLen_eq_of : SuffixEq c → ¬ SuffixEq (c+1) → lcsLen = c`.
* `run_rectangle_offset_eq` itself genuinely needs `0 < a ∧ 0 < c`; the
  initial-row/column extension is stated separately as
  `RunRectangleInitial.run_rectangle_offset_eq_leftCtx`, where `Repair.leftCtx`
  supplies the guarded base context.

## `ROSA_Credit_New_Results` (new credit-derivation package, 2026-09-24)

Five Std-only modules formalize the four proven conclusions of
`ROSA_Credit_New_Results.md` on top of the existing Phase-F/G/H assets.  They
depend only on the run-compressed core (`Lcs`, `RunRectangle`, `Repair`,
`RunRectangleLcp`, `RosBridge`, `Route`) — no new axioms, no `sorry`.

| note | statement | Lean theorem |
|---|---|---|
| §1 | strict-interior Q-owner: non-right-end K-centre ⇒ `R = 0` | `CreditRepair.right_ctx_zero_of_not_right_end` |
| §1 | `R > 0 ⇒ u = d` | `CreditRepair.carry_forces_k_right_end` |
| §1 | only the K-right-end representative survives birth | `CreditRepair.qOwnerBridges_carry_unique` |
| §1 | two retained candidates reproduce the whole envelope | `CreditRepair.two_candidates_reproduce_envelope` |
| §1 | at most two candidates per strict-interior Q-owner | `CreditCandidateCount.strictInterior_keep_le_two` |
| §2 | `Σ per-owner bounds ≤ #owners × bound` | `CreditCandidateCount.sum_map_le_card_mul` |
| §2 | ordered runs occupy ≤ `T` positions (and ≤ `T` interiors) | `CreditCandidateCount.sum_len_le_of_ordered`, `sum_interior_le_of_ordered` |
| §2 | `C ≤ T(5·R_Q+4·R_K) ≤ 5·T(R_Q+R_K)` | `CreditCandidateCount.repair_candidate_bound`, `repair_candidate_bound'` |
| §3 | priority is time-independent along a lifetime | `QEExpiry.bridge_rle_const` |
| §3 | expiry sweep tiles `[p, max death]`, ≤ 1 segment per candidate | `QEExpiry.scanAll_covered`, `scanAll_length_le` |
| §3 | each emitted segment's label is the live ROSA winner | `QEExpiry.qExpirySkyline_spec` |
| §4 | block coefficient `s+B-1+δ` = shifted block dot product | `CreditBlockConv.convCoeff_eq_blockDot` |
| §4 | full-block range = sum of block values (block prefixes) | `CreditBlockConv.blockDecomposition` |
| §4 | `D`-channel form | `CreditBlockConv.chanConv_eq_chanDot` |
| §4 | `⌈T/B⌉` covers `T`; `B² = a/b` balances `a/B` and `b·B` | `CreditBlockConv.nBlocks_mul_ge`, `nBlocks_le`, `balance_div`, `balance_sum` |
| §5 | modulus product `> 2·H_g` ⇒ unique signed recovery | `CreditCRT.crt_unique`, `crt_unique_three` |

Scope note: the note's asymptotic complexity claims (§2/§4 time bounds, the
`Õ(D T^{3/2})` full-credit bound) are **not** formalized as asymptotic analysis —
this package machine-checks the *mathematical content* those bounds rest on (the
candidate-count identity, the block-convolution identity and its cost balance,
and the exact-recovery condition), and leaves the arithmetic-model cost accounting
to the accompanying prose.
