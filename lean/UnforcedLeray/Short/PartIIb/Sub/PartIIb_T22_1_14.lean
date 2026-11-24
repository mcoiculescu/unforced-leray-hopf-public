import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # `PartII-b:T22/1/14` (`PicardIterates`): decomposition

Source: SP 2074-2093 (the cylinder equation `ω_σ = νΔω - v·∇ω`) and 2103-2105 ("smoothing");
the statements are standard heat-kernel / Volterra calculus (Picard iteration with the singular
kernel `(σ-r)^{-1/2}`).

Route (all in `picardIterates_of`).  `U 0 = H f`, `U (n+1) = duhamelMap (U n)`, `g 0 = U 0`,
`g (n+1) = U (n+1) - U n`, `Φ u = duhamelConv ν s (transp v u)`.  Then `g (n+1) = - Φ (g n)` on
`[s, T]` (`DuhamelPhiSub`) and, with `q = K1 K2 (1 + √L) Γ(1/2)`, `L = T - s`, the bound
`W2 (g m σ) cosh ≤ e m σ = B0 q^m (σ-s)^{m/2} / Γ(m/2 + 1)` follows from `PicStep` and
`VolterraStepBound` by induction.  `W2 (U n) cosh ≤ ∑_{k ≤ n} e k`, so all iterates lie in one class,
and `ε k = B0 (q √L)^k / Γ(k/2+1)` is summable (`GammaSeriesSummable`). -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

/-- `PicClass` without the size bound. -/
structure PicReg (c s T : ℝ) (u : ℝ → Pl → ℝ) : Prop where
  c2 : ∀ σ ∈ Icc s T, ContDiff ℝ 2 (u σ)
  periodic : ∀ σ ∈ Icc s T, ∀ x : Pl, u σ (x.1 + c, x.2) = u σ x
  cont0 : ContinuousOn (fun z : ℝ × Pl => u z.1 z.2) (Icc s T ×ˢ univ)
  cont1 : ∀ j : Fin 2,
    ContinuousOn (fun z : ℝ × Pl => B0579.pd j (u z.1) z.2) (Icc s T ×ˢ univ)
  cont2 : ∀ i j : Fin 2,
    ContinuousOn (fun z : ℝ × Pl => B0579.pd i (B0579.pd j (u z.1)) z.2) (Icc s T ×ˢ univ)

theorem PicReg.toClass {c s T B : ℝ} {u : ℝ → Pl → ℝ} (h : PicReg c s T u)
    (hb : ∀ σ ∈ Icc s T, ∀ x : Pl, W2 (u σ) x * Real.cosh x.2 ≤ B) : PicClass c s T B u :=
  ⟨h.c2, h.periodic, h.cont0, h.cont1, h.cont2, hb⟩

/-- **Leaf `PicRegSub`**: the regularity class is closed under differences (`pd` is linear on
`C²` slices, so the first and second partials of `a - b` are the differences of the partials). -/
def PicRegSub : Prop := ∀ (c s T : ℝ) (a b : ℝ → Pl → ℝ), PicReg c s T a → PicReg c s T b →
  PicReg c s T (fun σ x => a σ x - b σ x)

/-- **Leaf `W2AddLe`**: `W2` is subadditive on `C²` functions. -/
def W2AddLe : Prop := ∀ a b : Pl → ℝ, ContDiff ℝ 2 a → ContDiff ℝ 2 b → ∀ x : Pl,
  W2 (fun y => a y + b y) x ≤ W2 a x + W2 b x

/-- **Leaf `W2Neg`**: `W2 (-g) = W2 g` (`fderiv` of a negative is the negative of `fderiv`). -/
def W2Neg : Prop := ∀ (g : Pl → ℝ) (x : Pl), W2 (fun y => -g y) x = W2 g x

/-- **Leaf `PicStep`** (SP 2074-2093; `ConvRegular` composed with `TranspClass`): there are
`K1, K2 ≥ 0`, depending only on `c ν s T v`, such that for `u` in the regularity class with
`W2 (u σ) cosh ≤ b σ` (`b ≥ 0` continuous on `[s, T]`), the transport integrand `transp v u` is of
class `FReg` with `|·| cosh, |∇·| cosh ≤ K2 b`, and `Φ u = duhamelConv ν s (transp v u)` is in the
regularity class with `W2 (Φ u σ) cosh ≤ K1 ∫_s^σ (1 + (σ-r)^{-1/2}) (K2 b r) dr`. -/
def PicStep : Prop :=
  ∀ (c ν s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec), 0 < c → 0 < ν → 0 ≤ s → s ≤ T →
    CylCoeff c T v → ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧
      ∀ (u : ℝ → Pl → ℝ) (b : ℝ → ℝ), PicReg c s T u → ContinuousOn b (Icc s T) →
        (∀ σ ∈ Icc s T, 0 ≤ b σ) →
        (∀ σ ∈ Icc s T, ∀ x : Pl, W2 (u σ) x * Real.cosh x.2 ≤ b σ) →
        PicReg c s T (duhamelConv ν s (transp v u)) ∧ FReg s T (transp v u) ∧
          (∀ r ∈ Icc s T, WB (K2 * b r) (transp v u r)) ∧
          ∀ σ ∈ Icc s T, ∀ x : Pl, W2 (duhamelConv ν s (transp v u) σ) x * Real.cosh x.2 ≤
            K1 * ∫ r in s..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * (K2 * b r)

/-- **Leaf `DuhamelPhiSub`** (linearity of `Φ`): for `C²` slices `u, w` whose transport integrands are
of class `FReg` and bounded in the weight, `Φ (u - w) = Φ u - Φ w` on `[s, T]`.  (`transp` is
linear on `C¹` slices; the integrands `r ↦ H_{ν(σ-r)} F(r) (x)` are interval integrable by
`convTD_Int`, so `integral_sub` applies; the integrands agree on `[s, σ] ⊆ [s, T]`.) -/
def DuhamelPhiSub : Prop :=
  ∀ (ν s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec), 0 < ν → s ≤ T →
    ∀ u w : ℝ → Pl → ℝ, (∀ r ∈ Icc s T, ContDiff ℝ 2 (u r)) → (∀ r ∈ Icc s T, ContDiff ℝ 2 (w r)) →
      FReg s T (transp v u) → FReg s T (transp v w) →
      (∃ B : ℝ, ∀ r ∈ Icc s T, WB B (transp v u r)) →
      (∃ B : ℝ, ∀ r ∈ Icc s T, WB B (transp v w r)) →
      ∀ σ ∈ Icc s T, ∀ x : Pl,
        duhamelConv ν s (transp v (fun r y => u r y - w r y)) σ x =
          duhamelConv ν s (transp v u) σ x - duhamelConv ν s (transp v w) σ x

/-- **Leaf `VolterraStepBound`** (the Beta-function step, `Infra/VolterraEvolution/Beta.lean`
`integral_kernel_mul_rpow`): for `s ≤ σ ≤ s + L`,
`∫_s^σ (1 + (σ-r)^{-1/2}) (r-s)^{n/2} dr ≤ (1 + √L) Γ(1/2) Γ(n/2+1)/Γ((n+1)/2+1) (σ-s)^{(n+1)/2}`
(`1 ≤ √L (σ-r)^{-1/2}` for `0 < σ - r ≤ L`, then the Beta integral). -/
def VolterraStepBound : Prop := ∀ (s L σ : ℝ) (n : ℕ), 0 ≤ L → s ≤ σ → σ ≤ s + L →
  ∫ r in s..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * (r - s) ^ ((n : ℝ) / 2) ≤
    (1 + Real.sqrt L) * Real.Gamma (1 / 2) * Real.Gamma ((n : ℝ) / 2 + 1) /
      Real.Gamma (((n : ℝ) + 1) / 2 + 1) * (σ - s) ^ (((n : ℝ) + 1) / 2)

/-- **Leaf `GammaSeriesSummable`**: `∑ a q^n / Γ(n/2 + 1)` converges for `q ≥ 0`
(`Γ(n/2+1) ≥ ⌊n/2⌋!`, compare with `Real.summable_pow_div_factorial`, or the ratio test). -/
def GammaSeriesSummable : Prop := ∀ a q : ℝ, 0 ≤ q →
  Summable (fun n : ℕ => a * q ^ n / Real.Gamma ((n : ℝ) / 2 + 1))

/-- **`PartII-b:T22/1/14`, conditional**: `PicardIterates` from the leaves and `FreePart`. -/
theorem picardIterates_of (h1 : PicRegSub) (h2 : W2AddLe) (h3 : W2Neg) (h4 : PicStep)
    (h5 : DuhamelPhiSub) (h6 : VolterraStepBound) (h7 : GammaSeriesSummable) (hF : FreePart) :
    PicardIterates := by
  intro c ν s T v f hc hν hs hsT hv hf
  obtain ⟨K1, K2, hK1, hK2, hStep⟩ := h4 c ν s T v hc hν hs hsT hv
  obtain ⟨hF1, hF2, -, -, hF5, hF6, hF7, ⟨B0', hB0'⟩, -⟩ := hF c ν s T f hc hν hsT hf
  set FF : ℝ → Pl → ℝ := fun σ => heatSG (ν * (σ - s)) f with hFFdef
  have hFFreg : PicReg c s T FF := ⟨hF1, hF2, hF5, hF6, hF7⟩
  set B0 : ℝ := max B0' 0 with hB0def
  have hB0nn : 0 ≤ B0 := le_max_right _ _
  have hL : 0 ≤ T - s := by linarith
  set q : ℝ := K1 * K2 * (1 + Real.sqrt (T - s)) * Real.Gamma (1 / 2) with hqdef
  have hG12 : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hq : 0 ≤ q := by positivity
  have hΓ : ∀ m : ℕ, 0 < Real.Gamma ((m : ℝ) / 2 + 1) := fun m =>
    Real.Gamma_pos_of_pos (by positivity)
  set e : ℕ → ℝ → ℝ := fun m σ =>
    B0 * q ^ m / Real.Gamma ((m : ℝ) / 2 + 1) * (σ - s) ^ ((m : ℝ) / 2) with hedef
  have he_cont : ∀ m, Continuous (e m) := fun m =>
    continuous_const.mul ((continuous_id.sub continuous_const).rpow_const
      (fun _ => Or.inr (by positivity)))
  have he_nn : ∀ m : ℕ, ∀ σ : ℝ, s ≤ σ → 0 ≤ e m σ := fun m σ h =>
    mul_nonneg (div_nonneg (mul_nonneg hB0nn (pow_nonneg hq m)) (hΓ m).le)
      (Real.rpow_nonneg (sub_nonneg.2 h) _)
  set ε : ℕ → ℝ := fun k => B0 * (q * Real.sqrt (T - s)) ^ k / Real.Gamma ((k : ℝ) / 2 + 1)
    with hεdef
  have hε_nn : ∀ k, 0 ≤ ε k := fun k =>
    div_nonneg (mul_nonneg hB0nn (pow_nonneg (mul_nonneg hq (Real.sqrt_nonneg _)) k)) (hΓ k).le
  have he_le : ∀ k : ℕ, ∀ σ ∈ Icc s T, e k σ ≤ ε k := by
    intro k σ hσ
    have h1' : (σ - s) ^ ((k : ℝ) / 2) ≤ (T - s) ^ ((k : ℝ) / 2) :=
      Real.rpow_le_rpow (sub_nonneg.2 hσ.1) (by linarith [hσ.2]) (by positivity)
    have h2' : (T - s) ^ ((k : ℝ) / 2) = Real.sqrt (T - s) ^ k := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL]
      congr 1
      ring
    have hc0 : 0 ≤ B0 * q ^ k / Real.Gamma ((k : ℝ) / 2 + 1) :=
      div_nonneg (mul_nonneg hB0nn (pow_nonneg hq k)) (hΓ k).le
    calc e k σ = B0 * q ^ k / Real.Gamma ((k : ℝ) / 2 + 1) * (σ - s) ^ ((k : ℝ) / 2) := rfl
      _ ≤ B0 * q ^ k / Real.Gamma ((k : ℝ) / 2 + 1) * (T - s) ^ ((k : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left h1' hc0
      _ = ε k := by
          rw [h2', hεdef]
          simp only [mul_pow]
          ring
  -- the iterates and the differences
  obtain ⟨U, hU0, hUs⟩ : ∃ U : ℕ → ℝ → Pl → ℝ, U 0 = FF ∧
      ∀ n, U (n + 1) = duhamelMap ν s v f (U n) :=
    ⟨fun n => Nat.rec FF (fun _ u => duhamelMap ν s v f u) n, rfl, fun _ => rfl⟩
  obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → ℝ → Pl → ℝ, g 0 = U 0 ∧
      ∀ n, g (n + 1) = fun σ x => U (n + 1) σ x - U n σ x :=
    ⟨fun n => Nat.casesOn n (U 0) (fun n σ x => U (n + 1) σ x - U n σ x), rfl, fun _ => rfl⟩
  have hUstep : ∀ n σ x, U (n + 1) σ x =
      FF σ x - duhamelConv ν s (transp v (U n)) σ x := by
    intro n σ x
    rw [hUs n]
    rfl
  have hgstep : ∀ n σ x, g (n + 1) σ x = U (n + 1) σ x - U n σ x := by
    intro n σ x
    rw [hgs n]
  have hU0x : ∀ σ x, U 0 σ x = FF σ x := fun σ x => by rw [hU0]
  have hcosh : ∀ x : Pl, 0 ≤ Real.cosh x.2 := fun x => (Real.cosh_pos _).le
  -- the Beta step
  have hbound : ∀ (m : ℕ), ∀ σ ∈ Icc s T,
      K1 * ∫ r in s..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * (K2 * e m r) ≤ e (m + 1) σ := by
    intro m σ hσ
    have hP := h6 s (T - s) σ m hL hσ.1 (by linarith [hσ.2])
    have hC : 0 ≤ K2 * (B0 * q ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) :=
      mul_nonneg hK2 (div_nonneg (mul_nonneg hB0nn (pow_nonneg hq m)) (hΓ m).le)
    have hint : ∫ r in s..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * (K2 * e m r) =
        (K2 * (B0 * q ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) *
          ∫ r in s..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * (r - s) ^ ((m : ℝ) / 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      simp only [hedef]
      ring
    rw [hint]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hC) hK1).trans (le_of_eq ?_)
    have hm := (hΓ m).ne'
    have hm1 : Real.Gamma (((m : ℝ) + 1) / 2 + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    simp only [hedef, hqdef]
    push_cast
    rw [pow_succ]
    field_simp
  -- facts about the transport integrand
  set Mn : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n + 1), ε k with hMn
  have hMn_nn : ∀ n, 0 ≤ Mn n := fun n => Finset.sum_nonneg fun k _ => hε_nn k
  have hsum_le : ∀ n, ∀ σ ∈ Icc s T, ∑ k ∈ Finset.range (n + 1), e k σ ≤ Mn n :=
    fun n σ hσ => Finset.sum_le_sum fun k _ => he_le k σ hσ
  have hFW : ∀ n, PicReg c s T (U n) →
      (∀ σ ∈ Icc s T, ∀ x : Pl, W2 (U n σ) x * Real.cosh x.2 ≤ Mn n) →
      FReg s T (transp v (U n)) ∧ ∃ B : ℝ, ∀ r ∈ Icc s T, WB B (transp v (U n) r) := by
    intro n hr hb
    obtain ⟨-, hFR, hWB, -⟩ := hStep (U n) (fun _ => Mn n) hr continuousOn_const
      (fun _ _ => hMn_nn n) hb
    exact ⟨hFR, K2 * Mn n, fun r hr' => hWB r hr'⟩
  have he0 : ∀ σ, e 0 σ = B0 := fun σ => by simp [hedef]
  -- the main induction
  have key : ∀ n : ℕ,
      PicReg c s T (U n) ∧
      (∀ σ ∈ Icc s T, ∀ x : Pl, W2 (U n σ) x * Real.cosh x.2 ≤ ∑ k ∈ Finset.range (n + 1), e k σ) ∧
      PicReg c s T (g n) ∧
      (∀ σ ∈ Icc s T, ∀ x : Pl, W2 (g n σ) x * Real.cosh x.2 ≤ e n σ) ∧
      (FReg s T (transp v (U n)) ∧ ∃ B : ℝ, ∀ r ∈ Icc s T, WB B (transp v (U n) r)) ∧
      (∀ σ ∈ Icc s T, ∀ x : Pl, g (n + 1) σ x = -duhamelConv ν s (transp v (g n)) σ x) := by
    intro n
    induction n with
    | zero =>
      have hi : PicReg c s T (U 0) := by rw [hU0]; exact hFFreg
      have hii : ∀ σ ∈ Icc s T, ∀ x : Pl, W2 (U 0 σ) x * Real.cosh x.2 ≤ e 0 σ := by
        intro σ hσ x
        rw [he0]
        have := hB0' σ hσ x
        have h' : W2 (U 0 σ) x * Real.cosh x.2 ≤ B0' := by rw [hU0]; exact this
        exact h'.trans (le_max_left _ _)
      have hii' : ∀ σ ∈ Icc s T, ∀ x : Pl, W2 (U 0 σ) x * Real.cosh x.2 ≤
          ∑ k ∈ Finset.range (0 + 1), e k σ := by
        intro σ hσ x
        simpa using hii σ hσ x
      refine ⟨hi, hii', ?_, ?_, hFW 0 hi (fun σ hσ x => (hii' σ hσ x).trans (hsum_le 0 σ hσ)), ?_⟩
      · rw [hg0]; exact hi
      · rw [hg0]; exact hii
      · intro σ hσ x
        rw [hgstep 0 σ x, hUstep 0 σ x, hg0, hU0x σ x]
        ring
    | succ n ih =>
      obtain ⟨hiU, hiiU, hiig, hivg, hFWn, hId⟩ := ih
      have hbcont : ContinuousOn (fun σ => ∑ k ∈ Finset.range (n + 1), e k σ) (Icc s T) :=
        (continuous_finsetSum _ fun k _ => he_cont k).continuousOn
      have hbnn : ∀ σ ∈ Icc s T, 0 ≤ ∑ k ∈ Finset.range (n + 1), e k σ :=
        fun σ hσ => Finset.sum_nonneg fun k _ => he_nn k σ hσ.1
      have hPhiU := (hStep (U n) (fun σ => ∑ k ∈ Finset.range (n + 1), e k σ) hiU hbcont hbnn
        hiiU).1
      have hUfun : U (n + 1) = fun σ x => FF σ x - duhamelConv ν s (transp v (U n)) σ x :=
        funext fun σ => funext fun x => hUstep n σ x
      have hUreg : PicReg c s T (U (n + 1)) := by
        rw [hUfun]
        exact h1 c s T FF _ hFFreg hPhiU
      have hgfun : g (n + 1) = fun σ x => U (n + 1) σ x - U n σ x :=
        funext fun σ => funext fun x => hgstep n σ x
      have hgreg : PicReg c s T (g (n + 1)) := by
        rw [hgfun]
        exact h1 c s T _ _ hUreg hiU
      have hiv : ∀ σ ∈ Icc s T, ∀ x : Pl, W2 (g (n + 1) σ) x * Real.cosh x.2 ≤ e (n + 1) σ := by
        intro σ hσ x
        have hΦ := (hStep (g n) (e n) hiig (he_cont n).continuousOn
          (fun σ hσ => he_nn n σ hσ.1) hivg).2.2.2 σ hσ x
        have hfun : g (n + 1) σ = fun y => -(duhamelConv ν s (transp v (g n)) σ y) :=
          funext fun y => hId σ hσ y
        rw [hfun, h3 (duhamelConv ν s (transp v (g n)) σ) x]
        exact hΦ.trans (hbound n σ hσ)
      have hii : ∀ σ ∈ Icc s T, ∀ x : Pl, W2 (U (n + 1) σ) x * Real.cosh x.2 ≤
          ∑ k ∈ Finset.range (n + 1 + 1), e k σ := by
        intro σ hσ x
        have hfun : U (n + 1) σ = fun y => U n σ y + g (n + 1) σ y :=
          funext fun y => by rw [hgstep n σ y]; ring
        have hadd := h2 (U n σ) (g (n + 1) σ) (hiU.c2 σ hσ) (hgreg.c2 σ hσ) x
        rw [hfun, Finset.sum_range_succ]
        calc W2 (fun y => U n σ y + g (n + 1) σ y) x * Real.cosh x.2
            ≤ (W2 (U n σ) x + W2 (g (n + 1) σ) x) * Real.cosh x.2 :=
              mul_le_mul_of_nonneg_right hadd (hcosh x)
          _ = W2 (U n σ) x * Real.cosh x.2 + W2 (g (n + 1) σ) x * Real.cosh x.2 := by ring
          _ ≤ _ := add_le_add (hiiU σ hσ x) (hiv σ hσ x)
      have hFW1 := hFW (n + 1) hUreg (fun σ hσ x => (hii σ hσ x).trans (hsum_le (n + 1) σ hσ))
      refine ⟨hUreg, hii, hgreg, hiv, hFW1, ?_⟩
      intro σ hσ x
      have hphi := h5 ν s T v hν hsT (U (n + 1)) (U n) hUreg.c2 hiU.c2 hFW1.1 hFWn.1 hFW1.2
        hFWn.2 σ hσ x
      rw [hgstep (n + 1) σ x, hUstep (n + 1) σ x, hUstep n σ x, hgfun, hphi]
      ring
  -- assembly
  have hsum : Summable ε := h7 B0 (q * Real.sqrt (T - s)) (mul_nonneg hq (Real.sqrt_nonneg _))
  have hUclass : ∀ n, PicClass c s T (∑' k, ε k) (U n) := by
    intro n
    refine (key n).1.toClass fun σ hσ x => ((key n).2.1 σ hσ x).trans ?_
    exact (hsum_le n σ hσ).trans (hsum.sum_le_tsum _ (fun k _ => hε_nn k))
  refine ⟨U, ∑' k, ε k, fun n => ε (n + 1), hUclass, ?_, ?_, ?_, ?_⟩
  · intro σ _
    rw [hU0]
  · intro n σ _ x
    rw [hUs n]
  · exact (summable_nat_add_iff 1).2 hsum
  · intro n σ hσ x
    have hfun : (fun y => U (n + 1) σ y - U n σ y) = g (n + 1) σ := by
      rw [hgs n]
    rw [hfun]
    exact ((key (n + 1)).2.2.2.1 σ hσ x).trans (he_le (n + 1) σ hσ)

end CylPDE

end UnforcedLeray.Short.IIb
