import Std

/-!
## Exact ROSA credit — §4 of `ROSA_Credit_New_Results`

*"任意 V：把移位区间内积离线分块"* — the shifted interval dot product

`F(l,h,δ) = Σ_{t=l}^{h} ⟨g_t, V_{t+δ}⟩`

is answered offline: cut `g` into length-`B` blocks, reverse each block,

`g̃_{b,j}[i] = g_{s+B-1-i,j}`   (`s = b·B`),

convolve it with `V` once, and read off coefficient `s + B - 1 + δ`; the full-block
part of any query is then a difference of two block prefixes.

This file formalizes, on a self-contained integer partial sum `sSum`:

* `convCoeff_eq_blockDot` — the block-convolution **identity** (coefficient
  `s + B - 1 + δ` is exactly `Σ_{t=s}^{s+B-1} g_t · V_{t+δ}`), including the
  index reflection `i ↦ B-1-i`;
* `blockDecomposition` — the full-block part of a range is a sum of block values
  (the "block-prefix difference" step);
* `chanConv_eq_chanDot` — the `D`-channel (list of channels) form;
* `nBlocks_mul_ge` / `nBlocks_le` — the block count of length `T`, and
  `balance_div` — the arithmetic behind `B ≈ T√(log T / M)`: at `B² = a / b`
  the two cost terms `a / B` and `b · B` are equal.
-/

namespace CreditBlockConv

/-! ### Integer partial sums -/

/-- `sSum f n = Σ_{i<n} f i`. -/
def sSum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sSum f n + f n

theorem sSum_zero (f : Nat → Int) : sSum f 0 = 0 := rfl

theorem sSum_succ (f : Nat → Int) (n : Nat) : sSum f (n + 1) = sSum f n + f n := rfl

theorem sSum_congr {f g : Nat → Int} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    sSum f n = sSum g n := by
  induction n with
  | zero => simp [sSum]
  | succ k ih => rw [sSum_succ, sSum_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sSum_add_fun (f g : Nat → Int) (n : Nat) :
    sSum (fun i => f i + g i) n = sSum f n + sSum g n := by
  induction n with
  | zero => simp [sSum]
  | succ k ih => rw [sSum_succ, sSum_succ, sSum_succ, ih]; omega

theorem sSum_const_mul (c : Int) (f : Nat → Int) (n : Nat) :
    sSum (fun i => c * f i) n = c * sSum f n := by
  induction n with
  | zero => simp [sSum]
  | succ k ih => rw [sSum_succ, sSum_succ, ih, Int.mul_add]

/-- Splitting a partial sum at `m`. -/
theorem sSum_add_split (f : Nat → Int) (m : Nat) :
    ∀ n, sSum f (m + n) = sSum f m + sSum (fun i => f (m + i)) n := by
  intro n
  induction n with
  | zero => simp [sSum]
  | succ k ih =>
    rw [Nat.add_succ, sSum_succ, ih, sSum_succ]
    omega

/-- Re-indexing a partial sum by a shift. -/
theorem sSum_shift (f : Nat → Int) (n c : Nat) :
    sSum (fun i => f (i + c)) n = sSum f (n + c) - sSum f c := by
  have h := sSum_add_split f c n
  have h' : sSum (fun i => f (c + i)) n = sSum (fun i => f (i + c)) n := by
    apply sSum_congr; intro i _; rw [Nat.add_comm]
  rw [h'] at h
  rw [Nat.add_comm c n] at h
  omega

/-- **Index reflection.**  Summing over `range B` is unchanged by reversing the
index (`i ↦ B-1-i`). -/
theorem sSum_reverse (B : Nat) (F : Nat → Int) :
    sSum (fun i => F (B - 1 - i)) B = sSum F B := by
  induction B generalizing F with
  | zero => simp [sSum]
  | succ k ih =>
    rw [sSum_succ, sSum_succ]
    simp only [Nat.add_sub_cancel]
    rw [Nat.sub_self]
    have h1 : sSum (fun i => F (k - i)) k
        = sSum (fun i => (fun j => F (j + 1)) (k - 1 - i)) k := by
      apply sSum_congr; intro i hi; congr 1; omega
    rw [h1, ih (fun j => F (j + 1))]
    have h2 : sSum (fun j => F (j + 1)) k = sSum F (k + 1) - sSum F 1 := sSum_shift F k 1
    rw [h2]
    have h3 : sSum F 1 = F 0 := by rw [sSum_succ, sSum_zero]; omega
    rw [h3, sSum_succ]
    omega

/-! ### The block identity -/

/-- Shifted interval dot product over a length-`B` block starting at `s`. -/
def blockDot (g v : Nat → Int) (s B δ : Nat) : Int :=
  sSum (fun i => g (s + i) * v (s + i + δ)) B

/-- The reversed block `g̃[i] = g (s + B-1-i)` (zero outside `[0,B)`). -/
def revBlock (g : Nat → Int) (s B : Nat) : Nat → Int :=
  fun i => if i < B then g (s + (B - 1 - i)) else 0

/-- Coefficient `s + B - 1 + δ` of the convolution of the reversed block of `g`
with `v` — the quantity the prototype computes with one NTT per block. -/
def convCoeff (g v : Nat → Int) (s B δ : Nat) : Int :=
  sSum (fun i => revBlock g s B i * v (s + B - 1 + δ - i)) B

/-- **§4, block-convolution identity.**  The `(s+B-1+δ)`-th convolution
coefficient of the reversed block equals the shifted dot product over the block. -/
theorem convCoeff_eq_blockDot (g v : Nat → Int) (s B δ : Nat) :
    convCoeff g v s B δ = blockDot g v s B δ := by
  unfold convCoeff
  have h1 : ∀ i, i < B →
      revBlock g s B i * v (s + B - 1 + δ - i)
        = g (s + (B - 1 - i)) * v (s + (B - 1 - i) + δ) := by
    intro i hi
    have hrev : revBlock g s B i = g (s + (B - 1 - i)) := by
      unfold revBlock; rw [if_pos hi]
    have hidx : s + B - 1 + δ - i = s + (B - 1 - i) + δ := by omega
    rw [hrev, hidx]
  rw [sSum_congr h1]
  exact sSum_reverse B (fun j => g (s + j) * v (s + j + δ))

/-! ### Full-block decomposition -/

/-- **§4, block decomposition.**  A range of `n·B` instants starting at `a` is the
sum of its `n` length-`B` block values: this is the "two block prefixes" step. -/
theorem sSum_blocks (f : Nat → Int) (a B : Nat) :
    ∀ n, sSum (fun i => f (a + i)) (n * B)
      = sSum (fun b => sSum (fun t => f (a + b * B + t)) B) n := by
  intro n
  induction n with
  | zero => simp [sSum]
  | succ k ih =>
    rw [Nat.succ_mul, sSum_add_split, ih, sSum_succ]
    congr 1
    apply sSum_congr
    intro t _
    rw [Nat.add_assoc]

/-- **§4, assembled block decomposition.**  The full-block part of a shifted dot
product range equals the sum of the per-block convolution coefficients. -/
theorem blockDecomposition (g v : Nat → Int) (a B δ n : Nat) :
    sSum (fun i => g (a + i) * v (a + i + δ)) (n * B)
      = sSum (fun b => convCoeff g v (a + b * B) B δ) n := by
  rw [sSum_blocks (fun i => g i * v (i + δ)) a B n]
  apply sSum_congr
  intro b _
  rw [convCoeff_eq_blockDot]
  apply sSum_congr
  intro t _
  show g (a + b * B + t) * v (a + b * B + t + δ)
      = g (a + b * B + t) * v (a + b * B + t + δ)
  rfl

/-! ### Multi-channel form -/

/-- Channel-summed block dot product (`D` channels). -/
def chanDot (G V : List (Nat → Int)) (s B δ : Nat) : Int :=
  (G.zipWith (fun g v => blockDot g v s B δ) V).sum

/-- Channel-summed block convolution coefficient. -/
def chanConv (G V : List (Nat → Int)) (s B δ : Nat) : Int :=
  (G.zipWith (fun g v => convCoeff g v s B δ) V).sum

/-- **§4, `D`-channel identity.**  The identity holds channel-by-channel, hence
also for the channel sum (the prototype's `Σ_j g̃_{b,j} * V_j`). -/
theorem chanConv_eq_chanDot (G V : List (Nat → Int)) (s B δ : Nat) :
    chanConv G V s B δ = chanDot G V s B δ := by
  unfold chanConv chanDot
  induction G generalizing V with
  | nil => simp
  | cons g G ih =>
    cases V with
    | nil => simp
    | cons v V =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      rw [convCoeff_eq_blockDot, ih V]

/-! ### Block count and the optimal-block arithmetic -/

/-- Number of length-`B` blocks covering `T` instants (`⌈T/B⌉`). -/
def nBlocks (T B : Nat) : Nat := (T + B - 1) / B

/-- The blocks cover the range. -/
theorem nBlocks_mul_ge (T B : Nat) (hB : 0 < B) : T ≤ nBlocks T B * B := by
  unfold nBlocks
  have h := Nat.div_add_mod (T + B - 1) B
  rw [Nat.mul_comm B] at h
  have hmod := Nat.mod_lt (T + B - 1) hB
  omega

/-- `⌈T/B⌉ ≤ T/B + 1`: the block count is at most `T/B + 1`. -/
theorem nBlocks_le (T B : Nat) (hB : 0 < B) : nBlocks T B ≤ T / B + 1 := by
  unfold nBlocks
  rw [Nat.div_le_iff_le_mul_add_pred hB]
  have h := Nat.div_add_mod T B
  have hmod := Nat.mod_lt T hB
  rw [Nat.mul_add] at *
  omega

/-- **§4, block-size balance.**  With `a = D·T²·log T` (the convolution work term
`a / B`) and `b = D·M` (the edge term `b · B`), the two terms are equal exactly at
`B² = a / b`: if `a = b · B · B` then `a / B = b · B`. -/
theorem balance_div (A M B : Nat) (hB : 0 < B) (h : A = M * B * B) :
    A / B = M * B := by
  rw [h]
  exact Nat.mul_div_left (M * B) hB

theorem balance_sum (A M B : Nat) (hB : 0 < B) (h : A = M * B * B) :
    A / B + M * B = 2 * (M * B) := by
  rw [balance_div A M B hB h]
  omega

end CreditBlockConv
