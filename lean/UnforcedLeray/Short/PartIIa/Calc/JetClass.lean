import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, jet-class calculus for the late residual table (task `PartII-a:R02/8/org`)

Source of record: `the November 2 reference manuscript`, lines 1243-1285 (coefficients
1249-1257; late residual table 1267-1280: "each entry denotes its `L^∞_η L^∞_q` bound with
normalized weight `⟨η/√s⟩^m`; an `η` derivative gains `s^{-1/2}`", 1269-1272; "every `q`
derivative is exponentially small", 1281), with Lemma `sct:heat` (lines 437-480) and the mean equations
`sct:mean` (lines 397-404).

The table is read as membership of the coefficients in *graded jet classes* of families of
profiles indexed by the train: a family `F : Fam` assigns to every train `tr : TrainSol ν c` a
profile `F ν c tr : ProfilePoint → ℝ` (for instance the stream profile `trainProfile tr.ψ`).

* `WW a F`: weighted late size `s^{-a}` (`WtdBound`, normalized weight `(1+η²/s)^m`, `s ≥ 1`),
  with a polynomial constant `polyConst C d ν c` uniform over BUC trains, `c = ν^{-ρ}`, `ν ≤ ν₀`,
  for every `ρ > 1/2` and every weight `m`.
* `WE F`: the same with the exponentially small size `e^{-κνs/c²}` (`ExpBound`).
* `JE n F`: `F` smooth for `s > 0`, `WE F`, and recursively `JE (n-1)` of `K F`, `∂_η F`, `∂_q F`.
* `JQ n a F`: `F` smooth for `s > 0`, `WW a F`, and recursively `JQ (n-1) a (K F)`,
  `JQ (n-1) (a+1/2) (∂_η F)` (an `η` derivative gains `s^{-1/2}`, `K` keeps the size), and
  `JE (n-1) (∂_q F)` (every `q` derivative is exponentially small).
  (`JQ` is the class called `JQ = JW ∧ JE ∘ ∂_q` in the design of `PartII-a:R02/8/org`; the
  `∂_q` branch is built into the recursion, so `JQ` is closed under `K` and `∂_η` without
  commutators.  All mean objects are `q`-independent, so the `d_q`-free class `JW` of the design
  is not needed separately: a statement "`X ∈ JW a`" of the design is "`∀ n, JQ n a X`" here.)

## Exports (for `PartII-a:R02/8`, `/9/org`, `/10/org`, `/11/org`, `/12/org`)

Namespace `UnforcedLeray.Short.PartIIa.Jet`.

Definitions: `Fam`, `famK F` (`K F`), `famEta F` (`∂_η F`), `famQ F` (`∂_q F`), `famNu F`
(`ν F`), `famShift k F` (`(K+k) F`, `= famK F + k • F` by `famShift_eq`), `JSmooth F`,
`LateEq F G` (equal for `s > 0`), `WW a F`, `WE F`, `JE n F`, `JQ n a F`; `Fam` has the pointwise
`+, -, *, •, 0` (Pi instances).

Proved here:
* `LateEq.refl/symm/trans/of_eq`, `JSmooth.congr`, `JSmooth.zero`, `WW.congr`, `WE.congr`;
* `WW.add`, `WW.smul`, `WW.neg`, `WE.add`, `WE.smul`, `WE.neg`, `WW.zero`, `WE.zero`;
* accessors `JQ.smooth`, `JQ.ww`, `JQ.k` (`K`), `JQ.eta` (`∂_η`), `JQ.q` (`∂_q`), `JQ.mk`, `JQ.mk0`,
  `JQ.down`, `JQ.cast`,
  `JQ.of_le`, and the same for `JE` (`JE.we`, …);
* `JetCalculus.*` (from the bundle `JetCalculus`): `qadd, qsmul, qneg, qsub, qnu, qmono, qmul,
  qofE, qcongr, eadd, esmul, eneg, esub, enu, emul, ezero, econgr, qshift, eshift, qmulE`;
* `JE_of_words (hW : WordShiftE) : ∀ n F, WordsE F → JE n F`,
  `JQ_of_words (hJ : JetCalculus) (hW : WordShiftW) : ∀ n a F, WordsW a F → JQ n a F`;
* **block extraction**: `lateStmt_grpW` (generic sizes `a, b, e`, from `WW a X`,
  `WW b (∂_η X)`, `WW e ((K+3)X)`, `WE (∂_q X)`), `lateStmt_grpE` (four `WE`'s),
  `lateStmt_of_JQ` (`JQ 1 a X ⟹ LateStmt (LateGrpW … a (a+1/2) a)`), `lateStmt_of_JE`
  (`JE 1 X ⟹ LateStmt (LateGrpE …)`), where `X ν c tr = coef ν (trainProfile tr.ψ)
  (trainProfile tr.p)` (`coefFam coef`).

Also proved here: `jCongr_of (h : LateEqOps) : JCongr`, `jeToJQ_of (h : WAbsorb) : JEToJQ`.

Statements (`Prop`s, proved by leaf tasks `PartII-a:R02/8/<k>`): `SmoothClosure`, `LateEqOps`,
`LinearOps`, `LeibnizMul`, `IterCalcComm`, `IterCalcLin`, `WAlgMisc`, `WAlgMul`, `WAbsorb`,
`JLin`, `JEMul`, `JQMul` (nonnegative sizes), `WordShiftE`, `WordShiftW`; the bundles
`JetCalculus` (fields `hcongr hlin hemul hqmul hofE`) and `JetToolkit` (all of the above; one
theorem `jetToolkit : JetToolkit` in `Calc/JetToolkitProof.lean`, task `PartII-a:R02/8/17`,
is what the blocks import).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (IsBUCTrain)

/-! ### Families and operators -/

/-- A family of profiles indexed by the train: `F ν c tr : ProfilePoint → ℝ`. -/
abbrev Fam : Type := ∀ ν c : ℝ, UnforcedLeray.B0140.TrainSol ν c → ProfilePoint → ℝ

/-- `K F`, `K = η∂_η + 2s∂_s` (`ageOperator`). -/
def famK (F : Fam) : Fam := fun ν c tr => ageOperator (F ν c tr)

/-- `∂_η F`. -/
def famEta (F : Fam) : Fam := fun ν c tr => partialEta (F ν c tr)

/-- `∂_q F`. -/
def famQ (F : Fam) : Fam := fun ν c tr => partialQ (F ν c tr)

/-- `ν F`. -/
def famNu (F : Fam) : Fam := fun ν c tr x => ν * F ν c tr x

/-- `(K + k) F` (`ageShift`). -/
def famShift (k : ℝ) (F : Fam) : Fam := fun ν c tr => ageShift k (F ν c tr)

theorem famShift_eq (k : ℝ) (F : Fam) : famShift k F = famK F + k • F := rfl

/-- Smooth for `s > 0`, for every BUC train with `ν, c > 0`. -/
def JSmooth (F : Fam) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
    ContDiffOn ℝ ∞ (F ν c tr) {x : ProfilePoint | 0 < x.2.2}

/-- Equality for `s > 0`, for every BUC train with `ν, c > 0`. -/
def LateEq (F G : Fam) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
    EqOn (F ν c tr) (G ν c tr) {x : ProfilePoint | 0 < x.2.2}

/-- **Weighted late size `s^{-a}`** (lines 1270-1271: normalized weight `⟨η/√s⟩^m`, `s ≥ 1`), uniform
over BUC trains with `c = ν^{-ρ}`, `ν ≤ ν₀`, with a constant polynomial in `c, ν⁻¹`. -/
def WW (a : ℝ) (F : Fam) : Prop :=
  ∀ (ρ : ℝ) (m : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (d : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), IsBUCTrain tr →
      WtdBound m (F ν (ν ^ (-ρ)) tr) a (polyConst C d ν (ν ^ (-ρ)))

/-- **Exponentially small late size `e^{-κνs/c²}`** (lines 1278, 1281), same uniformity. -/
def WE (F : Fam) : Prop :=
  ∀ (ρ : ℝ) (m : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (d : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), IsBUCTrain tr →
      ExpBound κ ν (ν ^ (-ρ)) m (F ν (ν ^ (-ρ)) tr) (polyConst C d ν (ν ^ (-ρ)))

/-- **Exponentially small jets of depth `n`**: `F` and every word of length `≤ n` in
`K, ∂_η, ∂_q` applied to `F` are smooth and exponentially small. -/
def JE : ℕ → Fam → Prop
  | 0, F => JSmooth F ∧ WE F
  | n + 1, F => JSmooth F ∧ WE F ∧ JE n (famK F) ∧ JE n (famEta F) ∧ JE n (famQ F)

/-- **Weighted jets of depth `n` and size `a`**: `F` has size `s^{-a}`; `K F` keeps the size,
`∂_η F` has size `s^{-a-1/2}`, `∂_q F` is exponentially small, recursively to depth `n`. -/
def JQ : ℕ → ℝ → Fam → Prop
  | 0, a, F => JSmooth F ∧ WW a F
  | n + 1, a, F => JSmooth F ∧ WW a F ∧ JQ n a (famK F) ∧ JQ n (a + 1 / 2) (famEta F) ∧
      JE n (famQ F)

/-! ### Elementary facts -/

theorem LateEq.refl (F : Fam) : LateEq F F := fun _ _ _ _ _ _ => eqOn_refl _ _

theorem LateEq.symm {F G : Fam} (h : LateEq F G) : LateEq G F :=
  fun ν c hν hc tr htr => (h ν c hν hc tr htr).symm

theorem LateEq.trans {F G H : Fam} (h₁ : LateEq F G) (h₂ : LateEq G H) : LateEq F H :=
  fun ν c hν hc tr htr => (h₁ ν c hν hc tr htr).trans (h₂ ν c hν hc tr htr)

theorem LateEq.of_eq {F G : Fam} (h : F = G) : LateEq F G := h ▸ LateEq.refl F

theorem JSmooth.congr {F G : Fam} (h : LateEq F G) (hF : JSmooth F) : JSmooth G :=
  fun ν c hν hc tr htr => (hF ν c hν hc tr htr).congr fun x hx => (h ν c hν hc tr htr hx).symm

theorem JSmooth.zero : JSmooth (0 : Fam) := fun _ _ _ _ _ _ => contDiffOn_const

theorem WtdBound.nonneg {m : ℕ} {X : ProfilePoint → ℝ} {a B : ℝ} (h : WtdBound m X a B) :
    0 ≤ B := by
  have h1 := h ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) (le_refl _)
  norm_num at h1
  exact (abs_nonneg _).trans h1

theorem ExpBound.nonneg {κ ν c : ℝ} {m : ℕ} {X : ProfilePoint → ℝ} {B : ℝ}
    (h : ExpBound κ ν c m X B) : 0 ≤ B := by
  have h1 := h ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) (le_refl _)
  have hpos := Real.exp_pos (-(κ * ν * ((0 : ℝ), ((0 : ℝ), (1 : ℝ))).2.2 / c ^ 2))
  have h0 : 0 ≤ (1 + ((0 : ℝ), ((0 : ℝ), (1 : ℝ))).2.1 ^ 2 / ((0 : ℝ), ((0 : ℝ), (1 : ℝ))).2.2) ^ m *
      |X ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))| :=
    mul_nonneg (pow_nonneg (by norm_num) _) (abs_nonneg _)
  exact (mul_nonneg_iff_of_pos_right hpos).1 (h0.trans h1)

theorem weight_nonneg (m : ℕ) {x : ProfilePoint} (hx : 1 ≤ x.2.2) :
    0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m :=
  pow_nonneg (by have := div_nonneg (sq_nonneg x.2.1) (by linarith : (0 : ℝ) ≤ x.2.2); linarith) m

theorem rpow_neg_pos {ν ρ : ℝ} (hν : 0 < ν) : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _

theorem WW.congr {a : ℝ} {F G : Fam} (h : LateEq F G) (hF : WW a F) : WW a G := by
  intro ρ m hρ
  obtain ⟨C, d, ν₀, hν₀, H⟩ := hF ρ m hρ
  refine ⟨C, d, ν₀, hν₀, fun ν hν hνle tr htr x hx => ?_⟩
  have he := h ν (ν ^ (-ρ)) hν (rpow_neg_pos hν) tr htr (show 0 < x.2.2 by linarith)
  rw [← he]
  exact H ν hν hνle tr htr x hx

theorem WE.congr {F G : Fam} (h : LateEq F G) (hF : WE F) : WE G := by
  intro ρ m hρ
  obtain ⟨C, d, κ, ν₀, hκ, hν₀, H⟩ := hF ρ m hρ
  refine ⟨C, d, κ, ν₀, hκ, hν₀, fun ν hν hνle tr htr x hx => ?_⟩
  have he := h ν (ν ^ (-ρ)) hν (rpow_neg_pos hν) tr htr (show 0 < x.2.2 by linarith)
  rw [← he]
  exact H ν hν hνle tr htr x hx

theorem polyConst_add (C C' : ℝ) (d : ℕ) (ν c : ℝ) :
    polyConst (C + C') d ν c = polyConst C d ν c + polyConst C' d ν c := by
  unfold polyConst; ring

theorem polyConst_le_max {C : ℝ} {d d' : ℕ} {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) (hd : d ≤ d') :
    polyConst C d ν c ≤ polyConst (max C 0) d' ν c :=
  polyConst_mono hν hc (le_max_left _ _) (le_max_right _ _) hd

theorem WW.add {a : ℝ} {F G : Fam} (hF : WW a F) (hG : WW a G) : WW a (F + G) := by
  intro ρ m hρ
  obtain ⟨C₁, d₁, ν₁, hν₁, H₁⟩ := hF ρ m hρ
  obtain ⟨C₂, d₂, ν₂, hν₂, H₂⟩ := hG ρ m hρ
  refine ⟨max C₁ 0 + max C₂ 0, max d₁ d₂, min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro ν hν hνle tr htr x hx
  have hc := rpow_neg_pos (ρ := ρ) hν
  have h1 := H₁ ν hν (hνle.trans (min_le_left _ _)) tr htr x hx
  have h2 := H₂ ν hν (hνle.trans (min_le_right _ _)) tr htr x hx
  have e1 := polyConst_le_max (C := C₁) hν hc (le_max_left d₁ d₂)
  have e2 := polyConst_le_max (C := C₂) hν hc (le_max_right d₁ d₂)
  have hs : 0 ≤ x.2.2 ^ (-a) := Real.rpow_nonneg (by linarith) _
  have hw := weight_nonneg m hx
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x + G ν (ν ^ (-ρ)) tr x| ≤ _
  rw [polyConst_add]
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x + G ν (ν ^ (-ρ)) tr x|
      ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| +
          (1 + x.2.1 ^ 2 / x.2.2) ^ m * |G ν (ν ^ (-ρ)) tr x| := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
    _ ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) * x.2.2 ^ (-a) + polyConst C₂ d₂ ν (ν ^ (-ρ)) * x.2.2 ^ (-a) :=
        add_le_add h1 h2
    _ ≤ (polyConst (max C₁ 0) (max d₁ d₂) ν (ν ^ (-ρ)) +
          polyConst (max C₂ 0) (max d₁ d₂) ν (ν ^ (-ρ))) * x.2.2 ^ (-a) := by
        rw [add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right e1 hs) (mul_le_mul_of_nonneg_right e2 hs)

theorem WW.smul {a : ℝ} {F : Fam} (k : ℝ) (hF : WW a F) : WW a (k • F) := by
  intro ρ m hρ
  obtain ⟨C, d, ν₀, hν₀, H⟩ := hF ρ m hρ
  refine ⟨|k| * C, d, ν₀, hν₀, ?_⟩
  intro ν hν hνle tr htr x hx
  have h := H ν hν hνle tr htr x hx
  have e : polyConst (|k| * C) d ν (ν ^ (-ρ)) = |k| * polyConst C d ν (ν ^ (-ρ)) := by
    unfold polyConst; ring
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |k * F ν (ν ^ (-ρ)) tr x| ≤ _
  rw [e, abs_mul]
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|k| * |F ν (ν ^ (-ρ)) tr x|)
      = |k| * ((1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x|) := by ring
    _ ≤ |k| * (polyConst C d ν (ν ^ (-ρ)) * x.2.2 ^ (-a)) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg k)
    _ = |k| * polyConst C d ν (ν ^ (-ρ)) * x.2.2 ^ (-a) := by ring

theorem neg_eq_smul (F : Fam) : -F = (-1 : ℝ) • F := by
  funext ν c tr x
  show -F ν c tr x = -1 * F ν c tr x
  ring

theorem sub_eq_add_neg' (F G : Fam) : F - G = F + -G := sub_eq_add_neg F G

theorem WW.neg {a : ℝ} {F : Fam} (hF : WW a F) : WW a (-F) := by
  rw [neg_eq_smul]; exact hF.smul _

theorem WW.zero (a : ℝ) : WW a (0 : Fam) := by
  intro ρ m _
  refine ⟨0, 0, 1, one_pos, fun ν _ _ tr _ x _ => ?_⟩
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(0 : ℝ)| ≤ polyConst 0 0 ν (ν ^ (-ρ)) * x.2.2 ^ (-a)
  simp [polyConst]

theorem WE.add {F G : Fam} (hF : WE F) (hG : WE G) : WE (F + G) := by
  intro ρ m hρ
  obtain ⟨C₁, d₁, κ₁, ν₁, hκ₁, hν₁, H₁⟩ := hF ρ m hρ
  obtain ⟨C₂, d₂, κ₂, ν₂, hκ₂, hν₂, H₂⟩ := hG ρ m hρ
  refine ⟨max C₁ 0 + max C₂ 0, max d₁ d₂, min κ₁ κ₂, min ν₁ ν₂, lt_min hκ₁ hκ₂,
    lt_min hν₁ hν₂, ?_⟩
  intro ν hν hνle tr htr x hx
  have hc := rpow_neg_pos (ρ := ρ) hν
  have h1 := ExpBound.mono' hν hc (min_le_left κ₁ κ₂) (polyConst_le_max (C := C₁) hν hc
    (le_max_left d₁ d₂)) (H₁ ν hν (hνle.trans (min_le_left _ _)) tr htr) x hx
  have h2 := ExpBound.mono' hν hc (min_le_right κ₁ κ₂) (polyConst_le_max (C := C₂) hν hc
    (le_max_right d₁ d₂)) (H₂ ν hν (hνle.trans (min_le_right _ _)) tr htr) x hx
  have hw := weight_nonneg m hx
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x + G ν (ν ^ (-ρ)) tr x| ≤ _
  rw [polyConst_add, add_mul]
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x + G ν (ν ^ (-ρ)) tr x|
      ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| +
          (1 + x.2.1 ^ 2 / x.2.2) ^ m * |G ν (ν ^ (-ρ)) tr x| := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
    _ ≤ _ := add_le_add h1 h2

theorem WE.smul {F : Fam} (k : ℝ) (hF : WE F) : WE (k • F) := by
  intro ρ m hρ
  obtain ⟨C, d, κ, ν₀, hκ, hν₀, H⟩ := hF ρ m hρ
  refine ⟨|k| * C, d, κ, ν₀, hκ, hν₀, ?_⟩
  intro ν hν hνle tr htr x hx
  have h := H ν hν hνle tr htr x hx
  have e : polyConst (|k| * C) d ν (ν ^ (-ρ)) = |k| * polyConst C d ν (ν ^ (-ρ)) := by
    unfold polyConst; ring
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |k * F ν (ν ^ (-ρ)) tr x| ≤ _
  rw [e, abs_mul]
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|k| * |F ν (ν ^ (-ρ)) tr x|)
      = |k| * ((1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x|) := by ring
    _ ≤ |k| * (polyConst C d ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg k)
    _ = _ := by ring

theorem WE.neg {F : Fam} (hF : WE F) : WE (-F) := by
  rw [neg_eq_smul]; exact hF.smul _

theorem WE.zero : WE (0 : Fam) := by
  intro ρ m _
  refine ⟨0, 0, 1, 1, one_pos, one_pos, fun ν _ _ tr _ x _ => ?_⟩
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(0 : ℝ)| ≤
    polyConst 0 0 ν (ν ^ (-ρ)) * Real.exp (-(1 * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))
  simp [polyConst]

/-! ### Accessors -/

theorem JE.smooth : ∀ {n : ℕ} {F : Fam}, JE n F → JSmooth F
  | 0, _, h => h.1
  | _ + 1, _, h => h.1

theorem JE.we : ∀ {n : ℕ} {F : Fam}, JE n F → WE F
  | 0, _, h => h.2
  | _ + 1, _, h => h.2.1

theorem JE.k {n : ℕ} {F : Fam} (h : JE (n + 1) F) : JE n (famK F) := h.2.2.1

theorem JE.eta {n : ℕ} {F : Fam} (h : JE (n + 1) F) : JE n (famEta F) := h.2.2.2.1

theorem JE.q {n : ℕ} {F : Fam} (h : JE (n + 1) F) : JE n (famQ F) := h.2.2.2.2

theorem JE.mk {n : ℕ} {F : Fam} (h₁ : JSmooth F) (h₂ : WE F) (h₃ : JE n (famK F))
    (h₄ : JE n (famEta F)) (h₅ : JE n (famQ F)) : JE (n + 1) F := ⟨h₁, h₂, h₃, h₄, h₅⟩

theorem JE.mk0 {F : Fam} (h₁ : JSmooth F) (h₂ : WE F) : JE 0 F := ⟨h₁, h₂⟩

theorem JE.down : ∀ {n : ℕ} {F : Fam}, JE (n + 1) F → JE n F
  | 0, _, h => ⟨h.1, h.2.1⟩
  | _ + 1, _, h => ⟨h.1, h.2.1, JE.down h.2.2.1, JE.down h.2.2.2.1, JE.down h.2.2.2.2⟩

theorem JE.of_le {m n : ℕ} {F : Fam} (hmn : m ≤ n) (h : JE n F) : JE m F := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih (JE.down h)

theorem JQ.smooth : ∀ {n : ℕ} {a : ℝ} {F : Fam}, JQ n a F → JSmooth F
  | 0, _, _, h => h.1
  | _ + 1, _, _, h => h.1

theorem JQ.ww : ∀ {n : ℕ} {a : ℝ} {F : Fam}, JQ n a F → WW a F
  | 0, _, _, h => h.2
  | _ + 1, _, _, h => h.2.1

theorem JQ.k {n : ℕ} {a : ℝ} {F : Fam} (h : JQ (n + 1) a F) : JQ n a (famK F) := h.2.2.1

theorem JQ.eta {n : ℕ} {a : ℝ} {F : Fam} (h : JQ (n + 1) a F) :
    JQ n (a + 1 / 2) (famEta F) := h.2.2.2.1

theorem JQ.q {n : ℕ} {a : ℝ} {F : Fam} (h : JQ (n + 1) a F) : JE n (famQ F) := h.2.2.2.2

theorem JQ.mk {n : ℕ} {a : ℝ} {F : Fam} (h₁ : JSmooth F) (h₂ : WW a F) (h₃ : JQ n a (famK F))
    (h₄ : JQ n (a + 1 / 2) (famEta F)) (h₅ : JE n (famQ F)) : JQ (n + 1) a F :=
  ⟨h₁, h₂, h₃, h₄, h₅⟩

theorem JQ.mk0 {a : ℝ} {F : Fam} (h₁ : JSmooth F) (h₂ : WW a F) : JQ 0 a F := ⟨h₁, h₂⟩

theorem JQ.down : ∀ {n : ℕ} {a : ℝ} {F : Fam}, JQ (n + 1) a F → JQ n a F
  | 0, _, _, h => ⟨h.1, h.2.1⟩
  | _ + 1, _, _, h => ⟨h.1, h.2.1, JQ.down h.2.2.1, JQ.down h.2.2.2.1, JE.down h.2.2.2.2⟩

theorem JQ.of_le {m n : ℕ} {a : ℝ} {F : Fam} (hmn : m ≤ n) (h : JQ n a F) : JQ m a F := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih (JQ.down h)

/-- Rewrite the size index. -/
theorem JQ.cast {n : ℕ} {a a' : ℝ} {F : Fam} (e : a = a') (h : JQ n a F) : JQ n a' F := e ▸ h

/-! ### Statements of the calculus (leaves `PartII-a:R02/8/<k>`) -/

/-- **Smoothness is preserved** by the pointwise operations and by `K, ∂_η, ∂_q` (on the open
set `{s > 0}`; `ContDiffOn.add/mul/const_smul`, `contDiffOn_fderiv_apply` of `Sub/R02_2.lean`). -/
def SmoothClosure : Prop :=
  ∀ F G : Fam, JSmooth F → JSmooth G →
    JSmooth (F + G) ∧ JSmooth (F * G) ∧ (∀ k : ℝ, JSmooth (k • F)) ∧ JSmooth (famNu F) ∧
      JSmooth (famK F) ∧ JSmooth (famEta F) ∧ JSmooth (famQ F)

/-- **The operators are local**: functions equal on the open set `{s > 0}` have equal
`K, ∂_η, ∂_q` there (`Filter.EventuallyEq.fderiv_eq`). -/
def LateEqOps : Prop :=
  ∀ F G : Fam, LateEq F G →
    LateEq (famK F) (famK G) ∧ LateEq (famEta F) (famEta G) ∧ LateEq (famQ F) (famQ G)

/-- **Linearity of `K, ∂_η, ∂_q` on smooth families** (`fderiv_add`, `fderiv_const_mul`, at points
with `s > 0`), and `K 0 = ∂_η 0 = ∂_q 0 = 0`. -/
def LinearOps : Prop :=
  ∀ F G : Fam, JSmooth F → JSmooth G → ∀ k : ℝ,
    LateEq (famK (F + G)) (famK F + famK G) ∧ LateEq (famEta (F + G)) (famEta F + famEta G) ∧
    LateEq (famQ (F + G)) (famQ F + famQ G) ∧
    LateEq (famK (k • F)) (k • famK F) ∧ LateEq (famEta (k • F)) (k • famEta F) ∧
    LateEq (famQ (k • F)) (k • famQ F) ∧
    LateEq (famK (famNu F)) (famNu (famK F)) ∧ LateEq (famEta (famNu F)) (famNu (famEta F)) ∧
    LateEq (famQ (famNu F)) (famNu (famQ F)) ∧
    LateEq (famK 0) 0 ∧ LateEq (famEta 0) 0 ∧ LateEq (famQ 0) 0

/-- **Leibniz rule** for `K` (a first-order operator: `K(XY) = KX·Y + X·KY`, lines 1267-1268 "the heat
identity … and Lemma `sct:heat`"), `∂_η`, `∂_q`, on smooth families (`fderiv_mul`, `s > 0`). -/
def LeibnizMul : Prop :=
  ∀ F G : Fam, JSmooth F → JSmooth G →
    LateEq (famK (F * G)) (famK F * G + F * famK G) ∧
    LateEq (famEta (F * G)) (famEta F * G + F * famEta G) ∧
    LateEq (famQ (F * G)) (famQ F * G + F * famQ G)

/-- **Iterated commutators on single profiles** (calculus on the open set `{s > 0}`; from
`ProfileCommutators` (`profileCommutators`, `Tasks/R02/Commutators.lean`) and the symmetry of
second derivatives `FluctuationProfile.profile_fderiv_comm_at`): for `f` smooth for `s > 0`,
`∂_q^b ∂_η f = ∂_η ∂_q^b f`, `∂_q^b K f = K ∂_q^b f`, `∂_η^a K f = (K + a) ∂_η^a f` (the
word reduction `∂_η K = (K+1)∂_η`). -/
def IterCalcComm : Prop :=
  ∀ f : ProfilePoint → ℝ, ContDiffOn ℝ ∞ f {x : ProfilePoint | 0 < x.2.2} → ∀ a b : ℕ,
    EqOn (partialQ^[b] (partialEta f)) (partialEta (partialQ^[b] f))
        {x : ProfilePoint | 0 < x.2.2} ∧
    EqOn (partialQ^[b] (ageOperator f)) (ageOperator (partialQ^[b] f))
        {x : ProfilePoint | 0 < x.2.2} ∧
    EqOn (partialEta^[a] (ageOperator f))
        (fun x => ageOperator (partialEta^[a] f) x + (a : ℝ) * (partialEta^[a] f) x)
        {x : ProfilePoint | 0 < x.2.2}

/-- **Words are local and linear on single profiles** (calculus on `{s > 0}`): the word
`K^ℓ ∂_η^a ∂_q^b` respects equality on `{s > 0}`, and is linear on functions smooth there. -/
def IterCalcLin : Prop :=
  (∀ (f g : ProfilePoint → ℝ), EqOn f g {x : ProfilePoint | 0 < x.2.2} → ∀ ℓ a b : ℕ,
    EqOn (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] f)))
      (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] g))) {x : ProfilePoint | 0 < x.2.2}) ∧
  (∀ (f g : ProfilePoint → ℝ), ContDiffOn ℝ ∞ f {x : ProfilePoint | 0 < x.2.2} →
    ContDiffOn ℝ ∞ g {x : ProfilePoint | 0 < x.2.2} → ∀ (k : ℝ) (ℓ a b : ℕ),
    EqOn (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] (fun x => f x + k * g x))))
      (fun x => (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] f))) x +
        k * (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] g))) x)
      {x : ProfilePoint | 0 < x.2.2}) ∧
  (∀ (f : ProfilePoint → ℝ), ContDiffOn ℝ ∞ f {x : ProfilePoint | 0 < x.2.2} →
    ∀ (k : ℝ) (ℓ a b : ℕ),
    EqOn (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] (fun x => k * f x))))
      (fun x => k * (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] f))) x)
      {x : ProfilePoint | 0 < x.2.2})

/-- **Size monotonicity and the factor `ν`** (`s ≥ 1`: `s^{-a} ≤ s^{-a'}` for `a' ≤ a`; for
`ν ≤ min ν₀ 1`, `|ν F| ≤ |F|`). -/
def WAlgMisc : Prop :=
  (∀ (a a' : ℝ) (F : Fam), a' ≤ a → WW a F → WW a' F) ∧
  (∀ (a : ℝ) (F : Fam), WW a F → WW a (famNu F)) ∧
  (∀ F : Fam, WE F → WE (famNu F))

/-- **Sizes multiply** (weight `(1+η²/s)^m |XY| ≤ ((1+η²/s)^m |X|)·|Y|`, the second factor at
weight `0`; `polyConst C d · polyConst C' d' = polyConst (C C') (d + d')`). -/
def WAlgMul : Prop :=
  (∀ (a a' : ℝ) (F G : Fam), WW a F → WW a' G → WW (a + a') (F * G)) ∧
  (∀ F G : Fam, WW 0 F → WE G → WE (F * G) ∧ WE (G * F))

/-- **Exponential smallness beats every power** (lines 439-446, the absorption
`s^k e^{-κνs/c²} ≤ k!(2c²/(κν))^k e^{-κνs/(2c²)}`; `expPowAbsorb`,
`Tasks/R02/FluctuationProfile/ExpPowAbsorb.lean`): `WE F ⟹ WW a F` for every `a`. -/
def WAbsorb : Prop := ∀ (a : ℝ) (F : Fam), WE F → WW a F

/-- **The classes are local** (they only see `s > 0`). -/
def JCongr : Prop :=
  (∀ (n : ℕ) (a : ℝ) (F G : Fam), LateEq F G → JQ n a F → JQ n a G) ∧
  (∀ (n : ℕ) (F G : Fam), LateEq F G → JE n F → JE n G)

/-- **Linear closure** of the classes, size monotonicity, and `0 ∈ JE`. -/
def JLin : Prop :=
  (∀ (n : ℕ) (a : ℝ) (F G : Fam), JQ n a F → JQ n a G → JQ n a (F + G)) ∧
  (∀ (n : ℕ) (a : ℝ) (F : Fam) (k : ℝ), JQ n a F → JQ n a (k • F)) ∧
  (∀ (n : ℕ) (a : ℝ) (F : Fam), JQ n a F → JQ n a (famNu F)) ∧
  (∀ (n : ℕ) (a a' : ℝ) (F : Fam), a' ≤ a → JQ n a F → JQ n a' F) ∧
  (∀ (n : ℕ) (F G : Fam), JE n F → JE n G → JE n (F + G)) ∧
  (∀ (n : ℕ) (F : Fam) (k : ℝ), JE n F → JE n (k • F)) ∧
  (∀ (n : ℕ) (F : Fam), JE n F → JE n (famNu F)) ∧
  (∀ n : ℕ, JE n (0 : Fam))

/-- **Exponentially small times bounded is exponentially small** (`JE × JE`, `JQ 0 × JE`). -/
def JEMul : Prop :=
  (∀ (n : ℕ) (F G : Fam), JE n F → JE n G → JE n (F * G)) ∧
  (∀ (n : ℕ) (F G : Fam), JQ n 0 F → JE n G → JE n (F * G) ∧ JE n (G * F))

/-- **Sizes add under products** (`JQ a × JQ a' ⊆ JQ (a + a')` for nonnegative sizes; the
`∂_q` branch `∂_q F · G + F · ∂_q G` uses `JQ a' ⊆ JQ 0` for `a' ≥ 0`). -/
def JQMul : Prop :=
  ∀ (n : ℕ) (a a' : ℝ) (F G : Fam), 0 ≤ a → 0 ≤ a' → JQ n a F → JQ n a' G →
    JQ n (a + a') (F * G)

/-- **Exponentially small jets have every size.** -/
def JEToJQ : Prop := ∀ (n : ℕ) (a : ℝ) (F : Fam), JE n F → JQ n a F

/-- **The jet-class calculus** used by the five coefficient blocks. -/
structure JetCalculus : Prop where
  hcongr : JCongr
  hlin : JLin
  hemul : JEMul
  hqmul : JQMul
  hofE : JEToJQ

/-! ### Two closure statements proved here -/

/-- The classes only see `s > 0` (`JCongr` from `LateEqOps`). -/
theorem jCongr_of (h : LateEqOps) : JCongr := by
  have hE : ∀ (n : ℕ) (F G : Fam), LateEq F G → JE n F → JE n G := by
    intro n
    induction n with
    | zero => exact fun F G hFG hF => ⟨hF.1.congr hFG, hF.2.congr hFG⟩
    | succ n ih =>
      intro F G hFG hF
      obtain ⟨hK, hEta, hQ⟩ := h F G hFG
      exact ⟨hF.1.congr hFG, hF.2.1.congr hFG, ih _ _ hK hF.2.2.1, ih _ _ hEta hF.2.2.2.1,
        ih _ _ hQ hF.2.2.2.2⟩
  refine ⟨?_, hE⟩
  intro n
  induction n with
  | zero => exact fun a F G hFG hF => ⟨hF.1.congr hFG, hF.2.congr hFG⟩
  | succ n ih =>
    intro a F G hFG hF
    obtain ⟨hK, hEta, hQ⟩ := h F G hFG
    exact ⟨hF.1.congr hFG, hF.2.1.congr hFG, ih _ _ _ hK hF.2.2.1, ih _ _ _ hEta hF.2.2.2.1,
      hE _ _ _ hQ hF.2.2.2.2⟩

/-- Exponentially small jets have every size (`JEToJQ` from `WAbsorb`). -/
theorem jeToJQ_of (h : WAbsorb) : JEToJQ := by
  intro n
  induction n with
  | zero => exact fun a F hF => ⟨hF.1, h a F hF.2⟩
  | succ n ih =>
    intro a F hF
    exact ⟨hF.1, h a F hF.2.1, ih a _ hF.2.2.1, ih _ _ hF.2.2.2.1, hF.2.2.2.2⟩

/-! ### Derived closure rules -/

namespace JetCalculus

variable (hJ : JetCalculus)
include hJ

theorem qcongr {n : ℕ} {a : ℝ} {F G : Fam} (h : LateEq F G) (hF : JQ n a F) : JQ n a G :=
  hJ.hcongr.1 n a F G h hF

theorem econgr {n : ℕ} {F G : Fam} (h : LateEq F G) (hF : JE n F) : JE n G :=
  hJ.hcongr.2 n F G h hF

theorem qadd {n : ℕ} {a : ℝ} {F G : Fam} (hF : JQ n a F) (hG : JQ n a G) : JQ n a (F + G) :=
  hJ.hlin.1 n a F G hF hG

theorem qsmul {n : ℕ} {a : ℝ} {F : Fam} (k : ℝ) (hF : JQ n a F) : JQ n a (k • F) :=
  hJ.hlin.2.1 n a F k hF

theorem qneg {n : ℕ} {a : ℝ} {F : Fam} (hF : JQ n a F) : JQ n a (-F) := by
  rw [neg_eq_smul]; exact hJ.qsmul _ hF

theorem qsub {n : ℕ} {a : ℝ} {F G : Fam} (hF : JQ n a F) (hG : JQ n a G) : JQ n a (F - G) := by
  rw [sub_eq_add_neg']; exact hJ.qadd hF (hJ.qneg hG)

theorem qnu {n : ℕ} {a : ℝ} {F : Fam} (hF : JQ n a F) : JQ n a (famNu F) :=
  hJ.hlin.2.2.1 n a F hF

theorem qmono {n : ℕ} {a a' : ℝ} {F : Fam} (h : a' ≤ a) (hF : JQ n a F) : JQ n a' F :=
  hJ.hlin.2.2.2.1 n a a' F h hF

theorem eadd {n : ℕ} {F G : Fam} (hF : JE n F) (hG : JE n G) : JE n (F + G) :=
  hJ.hlin.2.2.2.2.1 n F G hF hG

theorem esmul {n : ℕ} {F : Fam} (k : ℝ) (hF : JE n F) : JE n (k • F) :=
  hJ.hlin.2.2.2.2.2.1 n F k hF

theorem eneg {n : ℕ} {F : Fam} (hF : JE n F) : JE n (-F) := by
  rw [neg_eq_smul]; exact hJ.esmul _ hF

theorem esub {n : ℕ} {F G : Fam} (hF : JE n F) (hG : JE n G) : JE n (F - G) := by
  rw [sub_eq_add_neg']; exact hJ.eadd hF (hJ.eneg hG)

theorem enu {n : ℕ} {F : Fam} (hF : JE n F) : JE n (famNu F) :=
  hJ.hlin.2.2.2.2.2.2.1 n F hF

theorem ezero (n : ℕ) : JE n (0 : Fam) := hJ.hlin.2.2.2.2.2.2.2 n

theorem emul {n : ℕ} {F G : Fam} (hF : JE n F) (hG : JE n G) : JE n (F * G) :=
  hJ.hemul.1 n F G hF hG

theorem qmulE {n : ℕ} {F G : Fam} (hF : JQ n 0 F) (hG : JE n G) : JE n (F * G) :=
  (hJ.hemul.2 n F G hF hG).1

theorem emulQ {n : ℕ} {F G : Fam} (hG : JE n G) (hF : JQ n 0 F) : JE n (G * F) :=
  (hJ.hemul.2 n F G hF hG).2

theorem qmul {n : ℕ} {a a' : ℝ} {F G : Fam} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hF : JQ n a F)
    (hG : JQ n a' G) : JQ n (a + a') (F * G) :=
  hJ.hqmul n a a' F G ha ha' hF hG

theorem qofE {n : ℕ} {F : Fam} (a : ℝ) (hF : JE n F) : JQ n a F := hJ.hofE n a F hF

/-- `(K + k)` keeps the weighted size (one level of depth). -/
theorem qshift {n : ℕ} {a : ℝ} {F : Fam} (k : ℝ) (hF : JQ (n + 1) a F) :
    JQ n a (famShift k F) := by
  rw [famShift_eq]; exact hJ.qadd hF.k (hJ.qsmul k hF.down)

/-- `(K + k)` keeps exponential smallness (one level of depth). -/
theorem eshift {n : ℕ} {F : Fam} (k : ℝ) (hF : JE (n + 1) F) : JE n (famShift k F) := by
  rw [famShift_eq]; exact hJ.eadd hF.k (hJ.esmul k hF.down)

end JetCalculus

/-! ### Jets from words (`K^ℓ ∂_η^a ∂_q^b` with `K` outermost, the form of the ingredients) -/

/-- The word `K^ℓ ∂_η^a ∂_q^b F` (the order of `LateFluctuationProfile`). -/
def wordE (ℓ a b : ℕ) (F : Fam) : Fam :=
  fun ν c tr => ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] (F ν c tr)))

/-- `F` is smooth and every word `K^ℓ ∂_η^a ∂_q^b F` is exponentially small. -/
def WordsE (F : Fam) : Prop := JSmooth F ∧ ∀ ℓ a b : ℕ, WE (wordE ℓ a b F)

/-- The word `K^ℓ ∂_η^b F` (the order of `LateMeanRemainder`). -/
def wordW (ℓ b : ℕ) (F : Fam) : Fam :=
  fun ν c tr => ageOperator^[ℓ] (partialEta^[b] (F ν c tr))

/-- `F` is smooth, `q`-independent for `s > 0` (`∂_q F = 0`), and every word `K^ℓ ∂_η^b F` has
size `s^{-a-b/2}`. -/
def WordsW (a : ℝ) (F : Fam) : Prop :=
  JSmooth F ∧ LateEq (famQ F) 0 ∧ ∀ ℓ b : ℕ, WW (a + (b : ℝ) / 2) (wordW ℓ b F)

/-- **Word reduction, exponential class**: `∂_q^b ∂_η = ∂_η ∂_q^b`, `∂_q^b K = K ∂_q^b`,
`∂_η^a K = (K + a)∂_η^a`, so `K^ℓ∂_η^a∂_q^b (K F) = K^{ℓ+1}∂_η^a∂_q^b F + a K^ℓ∂_η^a∂_q^b F`,
`K^ℓ∂_η^a∂_q^b (∂_η F) = K^ℓ∂_η^{a+1}∂_q^b F`, `K^ℓ∂_η^a∂_q^b (∂_q F) = K^ℓ∂_η^a∂_q^{b+1} F`
for `s > 0`. -/
def WordShiftE : Prop :=
  ∀ F : Fam, WordsE F → WordsE (famK F) ∧ WordsE (famEta F) ∧ WordsE (famQ F)

/-- **Word reduction, weighted class**: `K^ℓ∂_η^b (K F) = K^{ℓ+1}∂_η^b F + b K^ℓ∂_η^b F`,
`K^ℓ∂_η^b(∂_η F) = K^ℓ∂_η^{b+1} F`, and `∂_q K F = K ∂_q F = 0`, `∂_q ∂_η F = ∂_η ∂_q F = 0`. -/
def WordShiftW : Prop :=
  ∀ (a : ℝ) (F : Fam), WordsW a F → WordsW a (famK F) ∧ WordsW (a + 1 / 2) (famEta F)

/-- **Everything the coefficient blocks use**: the calculus statements and the class closure
(one theorem `jetToolkit : JetToolkit`, task `PartII-a:R02/8/17`, file
`Calc/JetToolkitProof.lean`). -/
structure JetToolkit : Prop where
  smooth : SmoothClosure
  eqOps : LateEqOps
  linOps : LinearOps
  leib : LeibnizMul
  comm : IterCalcComm
  iterLin : IterCalcLin
  wmisc : WAlgMisc
  wmul : WAlgMul
  wabs : WAbsorb
  jc : JetCalculus
  wordE : WordShiftE
  wordW : WordShiftW

theorem JE_of_words (hW : WordShiftE) : ∀ (n : ℕ) (F : Fam), WordsE F → JE n F
  | 0, _, h => ⟨h.1, h.2 0 0 0⟩
  | n + 1, F, h => by
    obtain ⟨hK, hEta, hQ⟩ := hW F h
    exact ⟨h.1, h.2 0 0 0, JE_of_words hW n _ hK, JE_of_words hW n _ hEta,
      JE_of_words hW n _ hQ⟩

theorem JQ_of_words (hJ : JetCalculus) (hW : WordShiftW) :
    ∀ (n : ℕ) (a : ℝ) (F : Fam), WordsW a F → JQ n a F
  | 0, a, F, h => by
    have e : a + ((0 : ℕ) : ℝ) / 2 = a := by simp
    have h0 := h.2.2 0 0
    rw [e] at h0
    exact ⟨h.1, h0⟩
  | n + 1, a, F, h => by
    have e : a + ((0 : ℕ) : ℝ) / 2 = a := by simp
    have h0 := h.2.2 0 0
    rw [e] at h0
    obtain ⟨hK, hEta⟩ := hW a F h
    exact ⟨h.1, h0, JQ_of_words hJ hW n a _ hK, JQ_of_words hJ hW n _ _ hEta,
      hJ.econgr h.2.1.symm (hJ.ezero n)⟩

/-! ### Block extraction and the `LateStmt` reduction -/

/-- The family of a residual coefficient `coef ν ψ p` evaluated on the train's stream and
pressure profiles. -/
def coefFam (coef : ℝ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → ProfilePoint → ℝ) : Fam :=
  fun ν _ tr => coef ν (trainProfile tr.ψ) (trainProfile tr.p)

/-- **Block extraction, weighted block** (lines 1269-1283): the four uniform bounds give the
`LateStmt` of the block `LateGrpW … a b e` (merge the four `(C, d, ν₀, κ)` by `max/min`). -/
theorem lateStmt_grpW
    (coef : ℝ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → ProfilePoint → ℝ) (a b e : ℝ)
    (h₁ : WW a (coefFam coef)) (h₂ : WW b (famEta (coefFam coef)))
    (h₃ : WW e (famShift 3 (coefFam coef))) (h₄ : WE (famQ (coefFam coef))) :
    LateStmt (fun ν c κ B m ψ p => LateGrpW m κ ν c B (coef ν ψ p) a b e) := by
  intro ρ m hρ
  obtain ⟨C₁, d₁, ν₁, hν₁, H₁⟩ := h₁ ρ m hρ
  obtain ⟨C₂, d₂, ν₂, hν₂, H₂⟩ := h₂ ρ m hρ
  obtain ⟨C₃, d₃, ν₃, hν₃, H₃⟩ := h₃ ρ m hρ
  obtain ⟨C₄, d₄, κ, ν₄, hκ, hν₄, H₄⟩ := h₄ ρ m hρ
  refine ⟨min (min ν₁ ν₂) (min ν₃ ν₄), lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄),
    max (max (max C₁ C₂) (max C₃ C₄)) 0, max (max d₁ d₂) (max d₃ d₄), κ, hκ, ?_⟩
  intro ν hν ψ p hψp
  obtain ⟨T, hT, rfl, rfl⟩ := hψp
  have hν0 : 0 < ν := hν.1
  have hc := rpow_neg_pos (ρ := ρ) hν0
  have hle : ν ≤ min (min ν₁ ν₂) (min ν₃ ν₄) := hν.2.le
  have hC0 : (0 : ℝ) ≤ max (max (max C₁ C₂) (max C₃ C₄)) 0 := le_max_right _ _
  have m1 : polyConst C₁ d₁ ν (ν ^ (-ρ)) ≤
      polyConst (max (max (max C₁ C₂) (max C₃ C₄)) 0) (max (max d₁ d₂) (max d₃ d₄)) ν
        (ν ^ (-ρ)) :=
    polyConst_mono hν0 hc (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
      hC0 ((le_max_left _ _).trans (le_max_left _ _))
  have m2 : polyConst C₂ d₂ ν (ν ^ (-ρ)) ≤
      polyConst (max (max (max C₁ C₂) (max C₃ C₄)) 0) (max (max d₁ d₂) (max d₃ d₄)) ν
        (ν ^ (-ρ)) :=
    polyConst_mono hν0 hc (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
      hC0 ((le_max_right _ _).trans (le_max_left _ _))
  have m3 : polyConst C₃ d₃ ν (ν ^ (-ρ)) ≤
      polyConst (max (max (max C₁ C₂) (max C₃ C₄)) 0) (max (max d₁ d₂) (max d₃ d₄)) ν
        (ν ^ (-ρ)) :=
    polyConst_mono hν0 hc (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
      hC0 ((le_max_left _ _).trans (le_max_right _ _))
  have m4 : polyConst C₄ d₄ ν (ν ^ (-ρ)) ≤
      polyConst (max (max (max C₁ C₂) (max C₃ C₄)) 0) (max (max d₁ d₂) (max d₃ d₄)) ν
        (ν ^ (-ρ)) :=
    polyConst_mono hν0 hc (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
      hC0 ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨WtdBound.mono' m1 (H₁ ν hν0 (hle.trans ((min_le_left _ _).trans (min_le_left _ _))) T hT),
    WtdBound.mono' m2 (H₂ ν hν0 (hle.trans ((min_le_left _ _).trans (min_le_right _ _))) T hT),
    WtdBound.mono' m3 (H₃ ν hν0 (hle.trans ((min_le_right _ _).trans (min_le_left _ _))) T hT),
    ExpBound.mono' hν0 hc le_rfl m4
      (H₄ ν hν0 (hle.trans ((min_le_right _ _).trans (min_le_right _ _))) T hT)⟩

/-- **Block extraction, exponentially small block** (line 1278, row `A₂`). -/
theorem lateStmt_grpE
    (coef : ℝ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → ProfilePoint → ℝ)
    (h₁ : WE (coefFam coef)) (h₂ : WE (famEta (coefFam coef)))
    (h₃ : WE (famShift 3 (coefFam coef))) (h₄ : WE (famQ (coefFam coef))) :
    LateStmt (fun ν c κ B m ψ p => LateGrpE m κ ν c B (coef ν ψ p)) := by
  intro ρ m hρ
  obtain ⟨C₁, d₁, κ₁, ν₁, hκ₁, hν₁, H₁⟩ := h₁ ρ m hρ
  obtain ⟨C₂, d₂, κ₂, ν₂, hκ₂, hν₂, H₂⟩ := h₂ ρ m hρ
  obtain ⟨C₃, d₃, κ₃, ν₃, hκ₃, hν₃, H₃⟩ := h₃ ρ m hρ
  obtain ⟨C₄, d₄, κ₄, ν₄, hκ₄, hν₄, H₄⟩ := h₄ ρ m hρ
  refine ⟨min (min ν₁ ν₂) (min ν₃ ν₄), lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄),
    max (max (max C₁ C₂) (max C₃ C₄)) 0, max (max d₁ d₂) (max d₃ d₄),
    min (min κ₁ κ₂) (min κ₃ κ₄), lt_min (lt_min hκ₁ hκ₂) (lt_min hκ₃ hκ₄), ?_⟩
  intro ν hν ψ p hψp
  obtain ⟨T, hT, rfl, rfl⟩ := hψp
  have hν0 : 0 < ν := hν.1
  have hc := rpow_neg_pos (ρ := ρ) hν0
  have hle : ν ≤ min (min ν₁ ν₂) (min ν₃ ν₄) := hν.2.le
  have hC0 : (0 : ℝ) ≤ max (max (max C₁ C₂) (max C₃ C₄)) 0 := le_max_right _ _
  have m1 : polyConst C₁ d₁ ν (ν ^ (-ρ)) ≤
      polyConst (max (max (max C₁ C₂) (max C₃ C₄)) 0) (max (max d₁ d₂) (max d₃ d₄)) ν
        (ν ^ (-ρ)) :=
    polyConst_mono hν0 hc (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
      hC0 ((le_max_left _ _).trans (le_max_left _ _))
  have m2 : polyConst C₂ d₂ ν (ν ^ (-ρ)) ≤
      polyConst (max (max (max C₁ C₂) (max C₃ C₄)) 0) (max (max d₁ d₂) (max d₃ d₄)) ν
        (ν ^ (-ρ)) :=
    polyConst_mono hν0 hc (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
      hC0 ((le_max_right _ _).trans (le_max_left _ _))
  have m3 : polyConst C₃ d₃ ν (ν ^ (-ρ)) ≤
      polyConst (max (max (max C₁ C₂) (max C₃ C₄)) 0) (max (max d₁ d₂) (max d₃ d₄)) ν
        (ν ^ (-ρ)) :=
    polyConst_mono hν0 hc (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
      hC0 ((le_max_left _ _).trans (le_max_right _ _))
  have m4 : polyConst C₄ d₄ ν (ν ^ (-ρ)) ≤
      polyConst (max (max (max C₁ C₂) (max C₃ C₄)) 0) (max (max d₁ d₂) (max d₃ d₄)) ν
        (ν ^ (-ρ)) :=
    polyConst_mono hν0 hc (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
      hC0 ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨ExpBound.mono' hν0 hc ((min_le_left _ _).trans (min_le_left _ _)) m1
      (H₁ ν hν0 (hle.trans ((min_le_left _ _).trans (min_le_left _ _))) T hT),
    ExpBound.mono' hν0 hc ((min_le_left _ _).trans (min_le_right _ _)) m2
      (H₂ ν hν0 (hle.trans ((min_le_left _ _).trans (min_le_right _ _))) T hT),
    ExpBound.mono' hν0 hc ((min_le_right _ _).trans (min_le_left _ _)) m3
      (H₃ ν hν0 (hle.trans ((min_le_right _ _).trans (min_le_left _ _))) T hT),
    ExpBound.mono' hν0 hc ((min_le_right _ _).trans (min_le_right _ _)) m4
      (H₄ ν hν0 (hle.trans ((min_le_right _ _).trans (min_le_right _ _))) T hT)⟩

/-- **Block extraction from a depth-one weighted jet**: `JQ 1 a X` gives the block
`LateGrpW … a (a+1/2) a` (`(K+3)X = KX + 3X` keeps the size). -/
theorem lateStmt_of_JQ
    (coef : ℝ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → ProfilePoint → ℝ) (a : ℝ)
    (h : JQ 1 a (coefFam coef)) :
    LateStmt (fun ν c κ B m ψ p => LateGrpW m κ ν c B (coef ν ψ p) a (a + 1 / 2) a) :=
  lateStmt_grpW coef a (a + 1 / 2) a h.ww h.eta.ww
    (by rw [famShift_eq]; exact h.k.ww.add (h.down.ww.smul 3)) h.q.we

/-- **Block extraction from a depth-one exponentially small jet.** -/
theorem lateStmt_of_JE
    (coef : ℝ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → ProfilePoint → ℝ)
    (h : JE 1 (coefFam coef)) :
    LateStmt (fun ν c κ B m ψ p => LateGrpE m κ ν c B (coef ν ψ p)) :=
  lateStmt_grpE coef h.we h.eta.we
    (by rw [famShift_eq]; exact h.k.we.add (h.down.we.smul 3)) h.q.we

end UnforcedLeray.Short.PartIIa.Jet
