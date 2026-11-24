import UnforcedLeray.Short.PartIIIb.NearInst.Targets

/-!
# Bins, restrictions and pieces of `near:deltaN` (source 3956-4053)

Source of record: `the November 2 reference manuscript`.  Concrete objects of the
proof of `near:deltaN` (proposition `near:equation-comparison`, lines 3927-3942, proof 3956-4053),
on the spaces of `Concrete/Spaces.lean` and the operators of `NearInst.lean`.

## Restrictions

* `ind A` : the indicator `1_A` of a set of chart points `(s, (q, η))`.
* `outRestr c A` : multiplication by `1_A` on `H` (an output restriction; `GainMul.mulBdd`); the
  zero operator for a non-measurable `A` (never used).
* `inRestr c mZ ρb A` : multiplication by `1_A` on both components of `Z` (an input restriction:
  inputs are tensors on `Z`, and the stress inverse acts on the sum of the components, source 3874).
* `fstZ`, `sndZ` : the projections `(T₁, T₂) ↦ (T₁, 0)`, `(T₁, T₂) ↦ (0, T₂)` of
  `Z = Z₁ ⊕ ρ_b^{-1/2}H_T` (thin and broad components, source 2698-2700).

## Regions (source 3958-3973, 3974-3985, 4013-4021)

* `ageBelow T = {s < T}`, `ageAbove T = {T ≤ s}` : output end regions `s < s₋`, `s ≥ S`
  (`s₋ = ε^a`, `S = ε^{-b}`, source 3933) and input regions `t < e^δ l` (complete block) and
  `t ≥ e^δ l` (partial strip and beyond, source 3978-3979).
* `binSet l r L = {l ≤ s < r, |η| ≤ L}` : an output bin inside the transverse box.
* `tailSet s₋ S L = {s₋ ≤ s < S, |η| > L}` : the transverse tail of the window.
* `transL C_⊥ c ν S = C_⊥(c/ν + √S + 1)` : the transverse cutoff `L_⊥` (source 3965-3967).
* `binCount s₋ S δ = ⌈4 log(S/s₋)/δ⌉₊ + 1` and `binEdge s₋ S N j = s₋ (S/s₋)^{j/N}` : the geometric
  partition of `[s₋, S]` into `N` bins `[l_j, r_j) = [binEdge j, binEdge (j+1))` with
  `r_j/l_j = (S/s₋)^{1/N} ≤ e^{δ/4} < e^{δ/2}` (source 3974-3977; `N` is polynomial in `ν⁻¹` in
  the regime since `log(S/s₋) = (a+b)d/ν`).

## Gained pieces (source 3875-3880, 4029-4031)

* `gainConjM γ hν M = G⁻¹ M g : H → Z` for a multiplier `M : H → Z`.
* `gainRestrM γ hν A M = G⁻¹ M 1_A g` (a multiplier restricted to output region `A`).
* `gainRestrS γ hν A X = g⁻¹ 1_A X G` (a response `X : Z → H` with output restricted to `A`).
* `gainBlockS γ hν A B X = g⁻¹ 1_A X 1_B G` (output region `A`, input region `B`).

Proved here: the restriction laws (`outRestr_univ_apply`, `outRestr_idem`), the split of the
input (`inRestr_below_add_above`), `fstZ_add_sndZ`, `gainConjS_sub`, the linearity of the chart
coefficient (`chartCoeff_split`) and the bin geometry (`binEdge_*`, `binCount_*`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst

/-! ## Indicators -/

/-- The indicator `1_A` of a set of chart points. -/
def ind (A : Set Chart) : Chart → ℝ := A.indicator fun _ => (1 : ℝ)

theorem ind_measurable {A : Set Chart} (hA : MeasurableSet A) : Measurable (ind A) :=
  measurable_const.indicator hA

theorem abs_ind_le (A : Set Chart) (p : Chart) : |ind A p| ≤ 1 := by
  unfold ind
  by_cases h : p ∈ A <;> simp [h]

theorem ind_mul_self (A : Set Chart) (p : Chart) : ind A p * ind A p = ind A p := by
  unfold ind
  by_cases h : p ∈ A <;> simp [h]

/-! ## Restriction operators -/

/-- Multiplication by `1_A` on `L²(μ; E)` (zero for a non-measurable `A`, never used). -/
def restrLp (μ : Measure Chart) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Set Chart) : Lp E 2 μ →L[ℝ] Lp E 2 μ := by
  classical
  exact if hA : MeasurableSet A then mulBdd (ind A) (ind_measurable hA) 1 (abs_ind_le A) else 0

section RestrLp

variable {μ : Measure Chart} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem restrLp_of_meas {A : Set Chart} (hA : MeasurableSet A) :
    restrLp μ E A = mulBdd (ind A) (ind_measurable hA) 1 (abs_ind_le A) := by
  unfold restrLp
  simp [hA]

theorem restrLp_ae {A : Set Chart} (hA : MeasurableSet A) (f : Lp E 2 μ) :
    (restrLp μ E A f : Chart → E) =ᵐ[μ] ind A • (f : Chart → E) := by
  rw [restrLp_of_meas hA]
  exact mulBdd_apply_ae _ _ _ _ f

/-- Two complementary indicator multipliers add up to the identity on `L²`. -/
theorem restrLp_add {A B : Set Chart} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ x, ind A x + ind B x = 1) (f : Lp E 2 μ) :
    restrLp μ E A f + restrLp μ E B f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (restrLp μ E A f) (restrLp μ E B f), restrLp_ae hA f,
    restrLp_ae hB f] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]
  change ind A x • (f : Chart → E) x + ind B x • (f : Chart → E) x = (f : Chart → E) x
  rw [← add_smul, hAB, one_smul]

theorem restrLp_univ_apply (f : Lp E 2 μ) : restrLp μ E univ f = f := by
  apply Lp.ext
  filter_upwards [restrLp_ae MeasurableSet.univ f] with x hx
  rw [hx]
  change ind univ x • (f : Chart → E) x = (f : Chart → E) x
  simp [ind]

theorem restrLp_idem {A : Set Chart} (hA : MeasurableSet A) (f : Lp E 2 μ) :
    restrLp μ E A (restrLp μ E A f) = restrLp μ E A f := by
  apply Lp.ext
  filter_upwards [restrLp_ae hA (restrLp μ E A f), restrLp_ae hA f] with x h1 h2
  rw [h1]
  change ind A x • (restrLp μ E A f : Chart → E) x = _
  rw [h2]
  change ind A x • (ind A x • (f : Chart → E) x) = ind A x • (f : Chart → E) x
  rw [smul_smul, ind_mul_self]

end RestrLp

/-- Output restriction: multiplication by `1_A` on `H`. -/
def outRestr (c : ℝ) (A : Set Chart) : Hsp c →L[ℝ] Hsp c :=
  restrLp (ageμ c (-3 / 2)) (EuclideanSpace ℝ (Fin 2)) A

theorem outRestr_univ_apply (c : ℝ) (u : Hsp c) : outRestr c univ u = u :=
  restrLp_univ_apply u

theorem outRestr_idem (c : ℝ) {A : Set Chart} (hA : MeasurableSet A) (u : Hsp c) :
    outRestr c A (outRestr c A u) = outRestr c A u :=
  restrLp_idem hA u

/-- The product equivalence of `Z = WithLp 1 (Z₁ × ρ_b^{-1/2}H_T)`. -/
abbrev zEquiv (c mZ ρb : ℝ) : Zsp c mZ ρb ≃L[ℝ] Z1sp c mZ × HTrho c ρb :=
  WithLp.prodContinuousLinearEquiv 1 ℝ (Z1sp c mZ) (HTrho c ρb)

/-- Input restriction: multiplication by `1_A` on both components of `Z`. -/
def inRestr (c mZ ρb : ℝ) (A : Set Chart) : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb :=
  ((zEquiv c mZ ρb).symm : Z1sp c mZ × HTrho c ρb →L[ℝ] Zsp c mZ ρb) ∘L
    ((restrLp (z1Measure c mZ) Ten3 A).prodMap (restrLp (htRhoMeasure c ρb) Ten3 A)) ∘L
    (zEquiv c mZ ρb : Zsp c mZ ρb →L[ℝ] Z1sp c mZ × HTrho c ρb)

theorem zEquiv_inRestr (c mZ ρb : ℝ) (A : Set Chart) (F : Zsp c mZ ρb) :
    zEquiv c mZ ρb (inRestr c mZ ρb A F) =
      (restrLp (z1Measure c mZ) Ten3 A (zEquiv c mZ ρb F).1,
        restrLp (htRhoMeasure c ρb) Ten3 A (zEquiv c mZ ρb F).2) := rfl

/-- The thin projection `(T₁, T₂) ↦ (T₁, 0)` of `Z`. -/
def fstZ (c mZ ρb : ℝ) : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb :=
  ((zEquiv c mZ ρb).symm : Z1sp c mZ × HTrho c ρb →L[ℝ] Zsp c mZ ρb) ∘L
    (ContinuousLinearMap.inl ℝ (Z1sp c mZ) (HTrho c ρb) ∘L
      ContinuousLinearMap.fst ℝ (Z1sp c mZ) (HTrho c ρb)) ∘L
    (zEquiv c mZ ρb : Zsp c mZ ρb →L[ℝ] Z1sp c mZ × HTrho c ρb)

/-- The broad projection `(T₁, T₂) ↦ (0, T₂)` of `Z`. -/
def sndZ (c mZ ρb : ℝ) : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb :=
  ((zEquiv c mZ ρb).symm : Z1sp c mZ × HTrho c ρb →L[ℝ] Zsp c mZ ρb) ∘L
    (ContinuousLinearMap.inr ℝ (Z1sp c mZ) (HTrho c ρb) ∘L
      ContinuousLinearMap.snd ℝ (Z1sp c mZ) (HTrho c ρb)) ∘L
    (zEquiv c mZ ρb : Zsp c mZ ρb →L[ℝ] Z1sp c mZ × HTrho c ρb)

theorem fstZ_add_sndZ (c mZ ρb : ℝ) (F : Zsp c mZ ρb) : fstZ c mZ ρb F + sndZ c mZ ρb F = F := by
  apply (zEquiv c mZ ρb).injective
  simp [fstZ, sndZ]
  rfl

/-! ## Regions -/

/-- `{s < T}`. -/
def ageBelow (T : ℝ) : Set Chart := {p | p.1 < T}

/-- `{T ≤ s}`. -/
def ageAbove (T : ℝ) : Set Chart := {p | T ≤ p.1}

/-- The output bin `{l ≤ s < r, |η| ≤ L}` (source 3974-3977, with the transverse box 3965-3967). -/
def binSet (l r L : ℝ) : Set Chart := {p | l ≤ p.1 ∧ p.1 < r ∧ |p.2.2| ≤ L}

/-- The transverse tail `{s₋ ≤ s < S, |η| > L}` of the window (source 3968-3973). -/
def tailSet (sm S L : ℝ) : Set Chart := {p | sm ≤ p.1 ∧ p.1 < S ∧ L < |p.2.2|}

theorem measurableSet_ageBelow (T : ℝ) : MeasurableSet (ageBelow T) :=
  measurableSet_lt measurable_fst measurable_const

theorem measurableSet_ageAbove (T : ℝ) : MeasurableSet (ageAbove T) :=
  measurableSet_le measurable_const measurable_fst

theorem measurable_absEta : Measurable fun p : Chart => |p.2.2| :=
  continuous_abs.measurable.comp (Measurable.snd measurable_snd)

theorem measurableSet_binSet (l r L : ℝ) : MeasurableSet (binSet l r L) :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_le measurable_absEta measurable_const))

theorem measurableSet_tailSet (sm S L : ℝ) : MeasurableSet (tailSet sm S L) :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const measurable_absEta))

theorem ind_below_add_above (T : ℝ) (x : Chart) : ind (ageBelow T) x + ind (ageAbove T) x = 1 := by
  unfold ind ageBelow ageAbove
  by_cases h : x.1 < T
  · have h' : ¬ T ≤ x.1 := not_le.2 h
    simp [Set.indicator, h, h']
  · have h' : T ≤ x.1 := not_lt.1 h
    simp [Set.indicator, h, h']

/-- The input split `1 = 1_{t<T} + 1_{t≥T}` on `Z` (complete block and the rest, source
3978-3979). -/
theorem inRestr_below_add_above (c mZ ρb T : ℝ) (F : Zsp c mZ ρb) :
    inRestr c mZ ρb (ageBelow T) F + inRestr c mZ ρb (ageAbove T) F = F := by
  apply (zEquiv c mZ ρb).injective
  have hA := measurableSet_ageBelow T
  have hB := measurableSet_ageAbove T
  rw [map_add, zEquiv_inRestr, zEquiv_inRestr, Prod.mk_add_mk,
    restrLp_add hA hB (ind_below_add_above T), restrLp_add hA hB (ind_below_add_above T)]

/-! ## The transverse cutoff and the bins (source 3965-3967, 3974-3977) -/

/-- `L_⊥ = C_⊥(c/ν + √S + 1)` (source 3965-3967). -/
def transL (Cperp c ν S : ℝ) : ℝ := Cperp * (c / ν + Real.sqrt S + 1)

/-- The number of bins `N = ⌈4 log(S/s₋)/δ⌉₊ + 1` (source 3974-3976). -/
def binCount (sm S δ : ℝ) : ℕ := ⌈4 * Real.log (S / sm) / δ⌉₊ + 1

/-- The bin edges `l_j = s₋ (S/s₋)^{j/N}` (`l_0 = s₋`, `l_N = S`). -/
def binEdge (sm S : ℝ) (N j : ℕ) : ℝ := sm * (S / sm) ^ ((j : ℝ) / N)

theorem binCount_pos (sm S δ : ℝ) : 0 < binCount sm S δ := Nat.succ_pos _

theorem binEdge_zero (sm S : ℝ) (N : ℕ) : binEdge sm S N 0 = sm := by
  simp [binEdge]

theorem binEdge_last {sm S : ℝ} (hsm : 0 < sm) {N : ℕ} (hN : N ≠ 0) : binEdge sm S N N = S := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  rw [binEdge, div_self hN', Real.rpow_one]
  field_simp

theorem one_le_ratio {sm S : ℝ} (hsm : 0 < sm) (hS : sm ≤ S) : 1 ≤ S / sm := by
  rw [le_div_iff₀ hsm]; linarith

theorem binEdge_ge {sm S : ℝ} (hsm : 0 < sm) (hS : sm ≤ S) (N j : ℕ) : sm ≤ binEdge sm S N j := by
  have h1 : 1 ≤ (S / sm) ^ ((j : ℝ) / N) := Real.one_le_rpow (one_le_ratio hsm hS) (by positivity)
  unfold binEdge
  nlinarith

theorem binEdge_lt_succ {sm S : ℝ} (hsm : 0 < sm) (hS : sm < S) {N : ℕ} (hN : N ≠ 0) (j : ℕ) :
    binEdge sm S N j < binEdge sm S N (j + 1) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  have hρ : 1 < S / sm := by rw [lt_div_iff₀ hsm]; linarith
  have hexp : (j : ℝ) / N < ((j + 1 : ℕ) : ℝ) / N := by
    apply div_lt_div_of_pos_right _ hN'
    push_cast; linarith
  unfold binEdge
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_exponent_lt hρ hexp) hsm

theorem binEdge_le_last {sm S : ℝ} (hsm : 0 < sm) (hS : sm ≤ S) {N j : ℕ} (hj : j ≤ N) :
    binEdge sm S N j ≤ S := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : j = 0 := by omega
    subst this
    rw [binEdge_zero]; exact hS
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hexp : (j : ℝ) / N ≤ 1 := by
    rw [div_le_one hN']; exact_mod_cast hj
  have h1 : (S / sm) ^ ((j : ℝ) / N) ≤ (S / sm) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_ratio hsm hS) hexp
  rw [Real.rpow_one] at h1
  calc binEdge sm S N j = sm * (S / sm) ^ ((j : ℝ) / N) := rfl
    _ ≤ sm * (S / sm) := mul_le_mul_of_nonneg_left h1 hsm.le
    _ = S := by field_simp

/-- The bin ratio: `l_{j+1} ≤ e^{δ/2} l_j` (source 3974-3975: `r/l < e^{δ/2}`). -/
theorem binEdge_succ_le {sm S δ : ℝ} (hsm : 0 < sm) (hS : sm ≤ S) (hδ : 0 < δ) (j : ℕ) :
    binEdge sm S (binCount sm S δ) (j + 1) ≤
      Real.exp (δ / 2) * binEdge sm S (binCount sm S δ) j := by
  set N := binCount sm S δ with hNdef
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (binCount_pos sm S δ)
  have hρ1 := one_le_ratio hsm hS
  have hρ : 0 < S / sm := by linarith
  have hlog : 0 ≤ Real.log (S / sm) := Real.log_nonneg hρ1
  have hceil : 4 * Real.log (S / sm) / δ ≤ N := by
    rw [hNdef, binCount]
    push_cast
    linarith [Nat.le_ceil (4 * Real.log (S / sm) / δ)]
  have hkey : Real.log (S / sm) * (1 / (N : ℝ)) ≤ δ / 2 := by
    rw [div_le_iff₀ hδ] at hceil
    rw [mul_one_div, div_le_iff₀ hN']
    nlinarith
  have hsplit : ((j + 1 : ℕ) : ℝ) / N = (j : ℝ) / N + 1 / N := by
    push_cast; ring
  have hstep : (S / sm) ^ (((j + 1 : ℕ) : ℝ) / N) =
      (S / sm) ^ ((j : ℝ) / N) * (S / sm) ^ (1 / (N : ℝ)) := by
    rw [hsplit, Real.rpow_add hρ]
  have hone : (S / sm) ^ (1 / (N : ℝ)) ≤ Real.exp (δ / 2) := by
    rw [Real.rpow_def_of_pos hρ]
    exact Real.exp_le_exp.2 hkey
  have hpos : 0 ≤ sm * (S / sm) ^ ((j : ℝ) / N) := by positivity
  unfold binEdge
  rw [hstep]
  calc sm * ((S / sm) ^ ((j : ℝ) / N) * (S / sm) ^ (1 / (N : ℝ)))
      = (sm * (S / sm) ^ ((j : ℝ) / N)) * (S / sm) ^ (1 / (N : ℝ)) := by ring
    _ ≤ (sm * (S / sm) ^ ((j : ℝ) / N)) * Real.exp (δ / 2) :=
        mul_le_mul_of_nonneg_left hone hpos
    _ = Real.exp (δ / 2) * (sm * (S / sm) ^ ((j : ℝ) / N)) := by ring

/-- The bin count: `N < 4 log(S/s₋)/δ + 2` (source 3975-3976). -/
theorem binCount_lt {sm S δ : ℝ} (hsm : 0 < sm) (hS : sm ≤ S) (hδ : 0 < δ) :
    (binCount sm S δ : ℝ) < 4 * Real.log (S / sm) / δ + 2 := by
  have hlog : 0 ≤ Real.log (S / sm) := Real.log_nonneg (one_le_ratio hsm hS)
  have h0 : 0 ≤ 4 * Real.log (S / sm) / δ := by positivity
  have := Nat.ceil_lt_add_one h0
  unfold binCount
  push_cast
  linarith

/-! ## Gained pieces (source 3875-3880, 4029-4031) -/

section Pieces

variable {c mZ ρb : ℝ}

/-- `G⁻¹ M g : H → Z` for a multiplier `M : H → Z`. -/
def gainConjM (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (M : Hsp c →L[ℝ] Zsp c mZ ρb) :
    Hsp c →L[ℝ] Zsp c mZ ρb :=
  ((gainEquiv c mZ ρb γ hν).symm : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb) ∘L M ∘L
    (gainH c γ hν : Hsp c →L[ℝ] Hsp c)

/-- `G⁻¹ M 1_A g`: a multiplier restricted to the output region `A`. -/
def gainRestrM (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (A : Set Chart) (M : Hsp c →L[ℝ] Zsp c mZ ρb) :
    Hsp c →L[ℝ] Zsp c mZ ρb :=
  gainConjM γ hν (M ∘L outRestr c A)

/-- `g⁻¹ 1_A X G`: a response `X : Z → H` with output restricted to `A`. -/
def gainRestrS (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (A : Set Chart) (X : Zsp c mZ ρb →L[ℝ] Hsp c) :
    Zsp c mZ ρb →L[ℝ] Hsp c :=
  gainConjS γ hν (outRestr c A ∘L X)

/-- `g⁻¹ 1_A X 1_B G`: a response with output region `A` and input region `B`. -/
def gainBlockS (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (A B : Set Chart) (X : Zsp c mZ ρb →L[ℝ] Hsp c) :
    Zsp c mZ ρb →L[ℝ] Hsp c :=
  gainConjS γ hν (outRestr c A ∘L X ∘L inRestr c mZ ρb B)

theorem gainConjS_apply (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (X : Zsp c mZ ρb →L[ℝ] Hsp c)
    (F : Zsp c mZ ρb) :
    gainConjS γ hν X F = (gainH c γ hν).symm (X (gainEquiv c mZ ρb γ hν F)) := rfl

theorem gainConjM_apply (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (M : Hsp c →L[ℝ] Zsp c mZ ρb) (u : Hsp c) :
    gainConjM γ hν M u = (gainEquiv c mZ ρb γ hν).symm (M (gainH c γ hν u)) := rfl

theorem gainRestrM_univ (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (M : Hsp c →L[ℝ] Zsp c mZ ρb) :
    gainRestrM γ hν univ M = gainConjM γ hν M := by
  ext1 u
  simp only [gainRestrM, gainConjM_apply, ContinuousLinearMap.comp_apply, outRestr_univ_apply]

theorem gainConjS_sub (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (X Y : Zsp c mZ ρb →L[ℝ] Hsp c) :
    gainConjS γ hν (X - Y) = gainConjS γ hν X - gainConjS γ hν Y := by
  ext1 F
  simp [gainConjS_apply]

end Pieces

/-! ## The chart coefficient of the exact split (source 2706, 2671) -/

/-- At ages `s ≥ 0` the chart coefficient of the train is its velocity. -/
theorem trainMer_eq {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (p : Chart) (hp : 0 ≤ p.1) :
    trainMer tr p = tr.v p.1 p.2 := by
  simp only [trainMer, UnforcedLeray.Short.IIIa.trainVel, if_pos hp]

/-- Linearity of the chart coefficient `v = s^{-1/2}V`: if `V = W + Σ α_i E_i` pointwise, then
`chartCoeff R V = chartCoeff R W + Σ α_i chartCoeff R E_i`. -/
theorem chartCoeff_add_sum (R : ℝ) (V W : ℝ → UnforcedLeray.SpatialField)
    (E : Fin 2 → ℝ → UnforcedLeray.SpatialField) (α : Fin 2 → ℝ)
    (h : ∀ τ y, V τ y = W τ y + ∑ i : Fin 2, α i • E i τ y) (pt : Chart) :
    UnforcedLeray.Short.IIIa.chartCoeff R V pt =
      UnforcedLeray.Short.IIIa.chartCoeff R W pt +
        ∑ i : Fin 2, α i • UnforcedLeray.Short.IIIa.chartCoeff R (E i) pt := by
  unfold UnforcedLeray.Short.IIIa.chartCoeff
  simp only [h, Fin.sum_univ_two]
  ext k
  fin_cases k <;> simp <;> ring

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
