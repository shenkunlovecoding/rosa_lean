import KDeleteROSA
import HookCut

/-!
## K-delete / abstract K-cut equivalence

For a fixed query endpoint `t`, the profile consumed by the abstract cut is

`lcsRow q k t e = (lcsLen q k t e : Int)`.

`rosaCand` contains every suffix-match route whose matched `K`-interval avoids
the owner `s`.  The interval's left endpoint is expressed in the
non-underflowing natural-number form `e + 1 - l`: when `l = e + 1` this is
`0`, so a route through `k[0]` is not admitted when `s = 0`.

`rosaCand` now scans exactly the same endpoints as `bruteKCut`, namely
`e < t`.  Its maximum is therefore equal to `bruteKCut` unconditionally.  The
historical `_of_pos_owner` wrappers below remain for API compatibility; their
old positivity and final-endpoint hypotheses are redundant.
-/

namespace KDeleteEquivalence

open Route Lcs RosBridge KDeleteAbstract KDeleteROSA CutArith HookCut

variable {α : Type} [DecidableEq α]

/-- The fixed-row length profile used by `CutArith`. -/
def lcsRow (q k : Nat → α) (t : Nat) : Nat → Int :=
  fun e => (lcsLen q k t e : Int)

/-- Casting `Nat.min` to `Int` commutes with `min`. -/
private theorem int_natCast_min (a b : Nat) :
    ((min a b : Nat) : Int) = min (a : Int) (b : Int) := by
  by_cases h : a ≤ b
  · rw [Nat.min_eq_left h, Int.min_eq_left (by exact_mod_cast h)]
  · have h' : b ≤ a := by omega
    rw [Nat.min_eq_right h', Int.min_eq_right (by exact_mod_cast h')]

private theorem valid_rosaCand {q k : Nat → α} {s t : Nat} {r : Route}
    (hr : r ∈ rosaCand q k s t) : Valid r := by
  obtain ⟨l, ep, _hl1, _hle, _hep, _hav, rfl⟩ := mem_rosaCand_fwd hr
  unfold Valid
  dsimp only
  exact ⟨by omega, by omega, by intro h; omega⟩

private theorem valid_rosaKDelete_best (q k : Nat → α) (s t : Nat) :
    Valid ((rosaKDelete q k s).best t) := by
  unfold KDeleteFamily.best
  exact valid_rmaxList _ (fun _ hr => valid_rosaCand hr)

/-- Every abstract K-cut candidate at an endpoint `e < t` is realized (or
dominated by the unmatched route) in `rosaKDelete` at the same time. -/
private theorem kcutCand_le_rosaKDelete_best (q k : Nat → α) (s t e : Nat)
    (he : e < t) :
    rle (kcutCand (lcsRow q k t) s e) ((rosaKDelete q k s).best t) := by
  unfold lcsRow kcutCand
  by_cases hlt : e < s
  · rw [if_pos hlt]
    by_cases hpos : 0 < (lcsLen q k t e : Int)
    · rw [mk_pos _ _ hpos]
      have hlen : 1 ≤ lcsLen q k t e := by omega
      have hmem : (⟨((lcsLen q k t e : Nat) : Int), (e : Int)⟩ : Route) ∈
          rosaCand q k s t :=
        mem_rosaCand_bwd hlen (Nat.le_refl _) he (Or.inl hlt)
      unfold KDeleteFamily.best
      exact rle_rmaxList _ _ hmem
    · rw [mk_nonpos _ _ (by
        show (lcsLen q k t e : Int) ≤ 0
        omega)]
      exact valid_rle_unmatched _ (valid_rosaKDelete_best q k s t)
  · rw [if_neg hlt]
    by_cases heq : e = s
    · rw [if_pos heq]
      exact valid_rle_unmatched _ (valid_rosaKDelete_best q k s t)
    · rw [if_neg heq]
      have hse : s < e := by omega
      by_cases hpos : 0 < min (lcsLen q k t e : Int) ((e : Int) - (s : Int))
      · rw [mk_pos _ _ hpos]
        let l : Nat := min (lcsLen q k t e) (e - s)
        have hsub : ((e - s : Nat) : Int) = (e : Int) - (s : Int) :=
          Int.ofNat_sub (by omega)
        have hcast : (l : Int) = min (lcsLen q k t e : Int) ((e : Int) - (s : Int)) := by
          dsimp only [l]
          rw [int_natCast_min, hsub]
        rw [← hcast]
        have hlpos : 1 ≤ l := by omega
        have hlen : l ≤ lcsLen q k t e := Nat.min_le_left _ _
        have hcap : l ≤ e - s := Nat.min_le_right _ _
        have hav : e < s ∨ s < e + 1 - l := by omega
        have hmem : (⟨(l : Int), (e : Int)⟩ : Route) ∈ rosaCand q k s t :=
          mem_rosaCand_bwd hlpos hlen he hav
        unfold KDeleteFamily.best
        exact rle_rmaxList _ _ hmem
      · rw [mk_nonpos _ _ (by
          show (min (lcsLen q k t e : Int) ((e : Int) - (s : Int))) ≤ 0
          omega)]
        exact valid_rle_unmatched _ (valid_rosaKDelete_best q k s t)

/-- Every ROSA candidate is below the corresponding abstract K-cut candidate.
The non-underflowing interval condition makes the former `l = e + 1` boundary
case ordinary: it is represented by left endpoint `0`, exactly as intended. -/
private theorem rosaCand_le_kcutCand {q k : Nat → α} {s t l ep : Nat}
    (hr : (⟨(l : Int), (ep : Int)⟩ : Route) ∈ rosaCand q k s t) :
    rle (⟨(l : Int), (ep : Int)⟩ : Route) (kcutCand (lcsRow q k t) s ep) := by
  obtain ⟨l', ep', hl1, hle, _hep, hav, hx⟩ := mem_rosaCand_fwd hr
  have hl : l = l' := by
    have := congrArg Route.len hx
    dsimp at this
    omega
  have hep : ep = ep' := by
    have := congrArg Route.endpoint hx
    dsimp at this
    omega
  subst hl
  subst hep
  have hleInt : (l : Int) ≤ (lcsLen q k t ep : Int) := by exact_mod_cast hle
  unfold lcsRow kcutCand
  by_cases hlt : ep < s
  · rw [if_pos hlt]
    have hpos : 0 < (lcsLen q k t ep : Int) := by omega
    rw [mk_pos _ _ hpos]
    unfold rle
    change (l : Int) < (lcsLen q k t ep : Int) ∨
      ((l : Int) = (lcsLen q k t ep : Int) ∧ (ep : Int) ≤ (ep : Int))
    rcases Int.lt_or_eq_of_le hleInt with hltLen | heqLen
    · exact Or.inl hltLen
    · exact Or.inr ⟨heqLen, Int.le_refl _⟩
  · rw [if_neg hlt]
    by_cases heq : ep = s
    · exfalso
      have hright : s < ep + 1 - l := by
        rcases hav with h | h
        · omega
        · exact h
      have hbad : s < s + 1 - l := by simpa [heq] using hright
      omega
    · rw [if_neg heq]
      have hse : s < ep := by omega
      have hright : s < ep + 1 - l := by
        rcases hav with h | h
        · omega
        · exact h
      have hle_ep : l ≤ ep := by omega
      have hsum : s + l < ep + 1 := (Nat.lt_sub_iff_add_lt).mp hright
      have hcapNat : l ≤ ep - s := by omega
      have hcap : (l : Int) ≤ (ep : Int) - (s : Int) := by omega
      have hcapPos : 0 < (ep : Int) - (s : Int) := by omega
      have hminpos : 0 < min (lcsLen q k t ep : Int) ((ep : Int) - (s : Int)) := by
        rw [Int.lt_min]
        exact ⟨by omega, hcapPos⟩
      rw [mk_pos _ _ hminpos]
      have hminle : (l : Int) ≤
          min (lcsLen q k t ep : Int) ((ep : Int) - (s : Int)) :=
        Int.le_min.mpr ⟨hleInt, hcap⟩
      unfold rle
      change (l : Int) < min (lcsLen q k t ep : Int) ((ep : Int) - (s : Int)) ∨
        ((l : Int) = min (lcsLen q k t ep : Int) ((ep : Int) - (s : Int)) ∧
          (ep : Int) ≤ (ep : Int))
      rcases Int.lt_or_eq_of_le hminle with hltLen | heqLen
      · exact Or.inl hltLen
      · exact Or.inr ⟨heqLen, Int.le_refl _⟩

/-- The always-valid lower bridge: `bruteKCut` is below the ROSA maximum. -/
theorem bruteKCut_le_rosaKDelete_best (q k : Nat → α) (s t : Nat) :
    rle (bruteKCut (lcsRow q k t) t s) ((rosaKDelete q k s).best t) := by
  unfold bruteKCut
  apply rmaxList_lub
  · exact valid_rosaKDelete_best q k s t
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨e, he, rfl⟩ := hr
    rw [List.mem_range] at he
    exact kcutCand_le_rosaKDelete_best q k s t e (by omega)

/-- ROSA's maximum is unconditionally below the brute K-cut: every ROSA
candidate has endpoint `e < t`, hence occurs in the brute scan. -/
theorem rosaKDelete_best_le_bruteKCut (q k : Nat → α) (s t : Nat) :
    rle ((rosaKDelete q k s).best t) (bruteKCut (lcsRow q k t) t s) := by
  unfold KDeleteFamily.best
  apply rmaxList_lub _ (bruteKCut (lcsRow q k t) t s)
    (valid_bruteKCut (lcsRow q k t) t s)
  intro r hr
  obtain ⟨l, ep, _hl1, _hle, hep, _hav, rfl⟩ := mem_rosaCand_fwd hr
  have hcand : rle (⟨(l : Int), (ep : Int)⟩ : Route)
      (kcutCand (lcsRow q k t) s ep) :=
    rosaCand_le_kcutCand (q := q) (k := k) (s := s) (t := t)
      (l := l) (ep := ep) hr
  have hbrute : rle (kcutCand (lcsRow q k t) s ep)
      (bruteKCut (lcsRow q k t) t s) := by
    unfold bruteKCut
    apply rle_rmaxList
    rw [List.mem_map]
    exact ⟨ep, by rw [List.mem_range]; exact hep, rfl⟩
  exact rle_trans _ _ _ hcand hbrute

/-- **Unconditional K-delete equivalence.**  The endpoint domains of
`rosaCand` and `bruteKCut` are exactly the same. -/
theorem rosaKDelete_best_eq_bruteKCut (q k : Nat → α) (s t : Nat) :
    (rosaKDelete q k s).best t = bruteKCut (lcsRow q k t) t s := by
  apply rle_antisymm
  · exact rosaKDelete_best_le_bruteKCut q k s t
  · exact bruteKCut_le_rosaKDelete_best q k s t

/-- Compatibility wrapper for the former positive-owner boundary theorem.
Its two hypotheses are retained only for the old call shape; they are not
needed by the corrected `e < t` domain. -/
theorem rosaKDelete_best_eq_bruteKCut_of_pos_owner (q k : Nat → α) (s t : Nat)
    (_hs : 0 < s)
    (_hlast : rle (kcutCand (lcsRow q k t) s t) (bruteKCut (lcsRow q k t) t s)) :
    (rosaKDelete q k s).best t = bruteKCut (lcsRow q k t) t s :=
  rosaKDelete_best_eq_bruteKCut q k s t

/-- Legacy wrapper for the old candidatewise boundary statement. -/
theorem rosaKDelete_best_le_bruteKCut_of_boundary (q k : Nat → α) (s t : Nat)
    (_hboundary : ∀ r, r ∈ rosaCand q k s t →
      rle r (bruteKCut (lcsRow q k t) t s)) :
    rle ((rosaKDelete q k s).best t) (bruteKCut (lcsRow q k t) t s) :=
  rosaKDelete_best_le_bruteKCut q k s t

/-- Hook-envelope form under the obsolete positive-owner boundary signature. -/
theorem rosaKDelete_best_eq_hookCut_of_pos_owner (q k : Nat → α) (s t : Nat)
    (_hs : 0 < s)
    (_hlast : rle (kcutCand (lcsRow q k t) s t) (bruteKCut (lcsRow q k t) t s)) :
    (rosaKDelete q k s).best t = hookCut (lcsRow q k t) t s := by
  rw [rosaKDelete_best_eq_bruteKCut q k s t,
    HookCut.kcut_hook_decomposition (lcsRow q k t) t s]

/-- **Unconditional hook-envelope form.** -/
theorem rosaKDelete_best_eq_hookCut (q k : Nat → α) (s t : Nat) :
    (rosaKDelete q k s).best t = hookCut (lcsRow q k t) t s := by
  rw [rosaKDelete_best_eq_bruteKCut q k s t,
    HookCut.kcut_hook_decomposition (lcsRow q k t) t s]

/-  The former boundary-conditioned equivalences were removed: with the
corrected `e < t` domain they would assert a genuine iff against an irrelevant
`e = t` condition, which is false. -/

/-- Bridge between the candidate-wise `Beats` predicate and comparison with the
`best` route. -/
theorem beats_iff_best_rle (D : KDeleteFamily) (b : Bridge) (t : Nat)
    (hb : b.Active t) :
    D.Beats b t ↔ rle (D.best t) (b.routeAt t) := by
  constructor
  · intro hbeats
    unfold KDeleteFamily.best
    exact rmaxList_lub (D.cand t) (b.routeAt t) (Bridge.valid_routeAt b t hb) hbeats
  · intro hbest r hr
    exact rle_trans r (D.best t) (b.routeAt t)
      (by
        unfold KDeleteFamily.best
        exact rle_rmaxList r (D.cand t) hr)
      hbest

/-- Concrete ROSA form of the `Beats`/`best` bridge, directly against the
abstract K-cut. -/
theorem rosaKDelete_beats_iff_bruteKCut_rle (q k : Nat → α) (s t : Nat) (b : Bridge)
    (hb : b.Active t) :
    (rosaKDelete q k s).Beats b t ↔
      rle (bruteKCut (lcsRow q k t) t s) (b.routeAt t) := by
  rw [beats_iff_best_rle]
  · rw [rosaKDelete_best_eq_bruteKCut q k s t]
  · exact hb

/-- The same `Beats` bridge under the obsolete positive-owner signature. -/
theorem rosaKDelete_beats_iff_bruteKCut_rle_of_pos_owner
    (q k : Nat → α) (s t : Nat) (b : Bridge) (_hs : 0 < s)
    (_hlast : rle (kcutCand (lcsRow q k t) s t) (bruteKCut (lcsRow q k t) t s))
    (hb : b.Active t) :
    (rosaKDelete q k s).Beats b t ↔
      rle (bruteKCut (lcsRow q k t) t s) (b.routeAt t) := by
  exact rosaKDelete_beats_iff_bruteKCut_rle q k s t b hb

end KDeleteEquivalence
