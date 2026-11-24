import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.DuhamelSplit
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf1Bound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.PairingCoV
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.ScaleMemLp
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.RhsCont.WeightedCS

/-!
# Helper for `FreeMovingDuality` (`PartIII-a:T21/c3/3/1/1/2/2/2`): corrected statement and assembly

Source `the November 2 reference manuscript` (SP) lines 2937-2958, 3036-3060.


fixes `U` only a.e. on cylinder data and bounds it through the lower integral `eLpNorm`, so
`U' g = U g + L g • 1_N` (`L` a `ℂ`-linear functional vanishing on the span of the continuous
cylinder images `movCx a f₁ f₂`, `N ⊆ C_{d(s)}` of inner measure zero and positive outer measure)
is again admissible; for `g` with `L g = 1` and `Γ = 1_B` (`B ⊇ N` a box) `U' s s g * Γ` is not
a.e. measurable, its Bochner integral is `0`, while the right side at `s₁ = s₂ = s` is `∫ g Γ`.
`PropagatorMeas` is the missing clause (the propagator built in `freeMovingPropagatorExists` is a
coerced `Lp` map, so it satisfies it by `Lp.aestronglyMeasurable`).

With that clause, `freeMovingDualityM_of` proves the corrected statement `FreeMovingDualityM` from
three leaves:
* `FreeAdjExists`: regular free adjoint flows exist (Volterra/parabolic construction);
* `FreeCylDuality`: the physical pairing identity for cylinder data (free analogue of
  `LinAdjDuality`);
* `CylDataDense`: complex cylinder data `movCx a f₁ f₂` are dense in `X_{m,c/√a}`.
The assembly uses `pairingCoV`, `physAdj_movingPhi`, `mpScaleMemLp`, `weightedCS` and the
boundedness and linearity clauses of `IsFreeMovingPropagator`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub ComplCouplingSub PerturbDuhamelSub

namespace ComplFreeRateSub

namespace Leaf2DualityNeeded

/-- **Leaf (existence)** (SP 2937-2958, 3060): every terminal datum `Γ ∈ X_{-m,d(s)}` has a regular
backward free adjoint flow on `[t₁, s]` (the free analogue of `AdjointWeakExists` +
`AdjointWeakRegular`, without the Biot-Savart term). -/
def FreeAdjExists (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ) :
    Prop :=
  8 < m → 0 < ν → 0 ≤ t₁ → t₁ ≤ t₂ → UnforcedLeray.Short.PartI.IsBUCTrain tr →
  ∀ s ∈ Icc t₁ t₂, ∀ Γ : ℝ × ℝ → ℂ, MemLp Γ 2 (B0579.cellMeasure (dd ν s) (-m)) →
    ∃ φ : ℝ → ℝ × ℝ → ℂ,
      IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ s (physAdj (clockA ν s) Γ) φ

/-- **Leaf (cylinder duality)** (SP 2937-2958): the physical pairing of a free cylinder flow from
`s₁` with a regular free adjoint flow on `[t₁, s]` is constant: `∫ ω(s) g = ∫ f φ(s₁)` (the free
analogue of `LinAdjDuality`). -/
def FreeCylDuality (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ) :
    Prop :=
  8 < m → 0 < ν → 0 ≤ t₁ → t₁ ≤ t₂ → UnforcedLeray.Short.PartI.IsBUCTrain tr →
  ∀ s ∈ Icc t₁ t₂, ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
    IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ s g φ →
    ∀ s₁ ∈ Icc t₁ s, ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
      ∀ ω : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f ω →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ((ω s x : ℝ) : ℂ) * g x =
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ((f x : ℝ) : ℂ) * φ s₁ x

/-- **Leaf (density)**: complex cylinder data `J_a⁻¹f₁ + iJ_a⁻¹f₂` are dense in `X_{m,c/√a}`. -/
def CylDataDense : Prop :=
  ∀ c a m : ℝ, 0 < c → 1 ≤ a → 0 ≤ m → ∀ g : ℝ × ℝ → ℂ,
    MemLp g 2 (B0579.cellMeasure (cellLen c a) m) → ∀ ε : ℝ, 0 < ε →
    ∃ f₁ f₂ : B0579.Plane → ℝ, B0579.IsCylTest c f₁ ∧ B0579.IsCylTest c f₂ ∧
      xNorm (cellLen c a) m (g - movCx a f₁ f₂) < ENNReal.ofReal ε

/-- `FreeMovingDuality` with the measurability clause `PropagatorMeas` on `U`. -/
def FreeMovingDualityM (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) : Prop :=
  8 < m → 0 < ν → 0 ≤ t₁ → t₁ ≤ t₂ → UnforcedLeray.Short.PartI.IsBUCTrain tr →
  ∀ U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ),
    IsFreeMovingPropagator ν m tr t₁ t₂ U → PropagatorMeas ν m t₁ t₂ U →
    FreeFlowAvail ν m tr t₁ t₂ →
    ∀ s₂ ∈ Icc t₁ t₂, ∀ Γ : ℝ × ℝ → ℂ, MemLp Γ 2 (B0579.cellMeasure (dd ν s₂) (-m)) →
      ∃ Φ : ℝ → ℝ × ℝ → ℂ, MovingFreeAdjoint ν m tr t₁ s₂ Γ Φ ∧
        ∀ s₁ ∈ Icc t₁ s₂, ∀ g : ℝ × ℝ → ℂ, MemLp g 2 (B0579.cellMeasure (dd ν s₁) m) →
          ∫ y in B0579.cell (dd ν s₂), U s₂ s₁ g y * Γ y =
            ∫ y in B0579.cell (dd ν s₁), g y * Φ s₁ y

/-- Weighted Cauchy-Schwarz for the unweighted cell pairing of `X_{m,d}` and `X_{-m,d}`. -/
theorem pair_bound {d m : ℝ} {A B : ℝ × ℝ → ℂ} (hA : MemLp A 2 (B0579.cellMeasure d m))
    (hB : MemLp B 2 (B0579.cellMeasure d (-m))) :
    Integrable (fun y => A y * B y) (volume.restrict (B0579.cell d)) ∧
      ‖∫ y in B0579.cell d, A y * B y‖ ≤ (xNorm d m A * xNorm d (-m) B).toReal := by
  have hcs := _root_.weightedCS d m B (fun y => ‖A y‖) hB.aestronglyMeasurable
    hA.aestronglyMeasurable.norm
  have hn : eLpNorm (fun y => ‖A y‖) 2 (B0579.cellMeasure d m) = xNorm d m A := eLpNorm_norm A
  rw [hn] at hcs
  have hlin : ∫⁻ y in B0579.cell d, ‖A y * B y‖ₑ =
      ∫⁻ y in B0579.cell d, ‖B y‖ₑ * ‖‖A y‖‖ₑ := by
    congr 1; funext y; rw [enorm_mul, enorm_norm, mul_comm]
  have hfin : xNorm d m A * xNorm d (-m) B < ⊤ := ENNReal.mul_lt_top hA.2 hB.2
  have hle : ∫⁻ y in B0579.cell d, ‖A y * B y‖ₑ ≤ xNorm d m A * xNorm d (-m) B := by
    rw [hlin, mul_comm (xNorm d m A)]; exact hcs
  refine ⟨⟨(hA.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure d m)).mul
      (hB.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure d (-m))),
      lt_of_le_of_lt hle hfin⟩, ?_⟩
  refine (norm_integral_le_lintegral_norm _).trans ?_
  refine ENNReal.toReal_mono hfin.ne ?_
  simpa [ofReal_norm] using hle

/-- The scaling `y ↦ √a y` maps the cell of length `c/√a` into the cell of length `c`. -/
theorem mem_cell_scale {c a : ℝ} (ha : 0 < a) {y : ℝ × ℝ}
    (hy : y ∈ B0579.cell (cellLen c a)) :
    (Real.sqrt a * y.1, Real.sqrt a * y.2) ∈ B0579.cell c := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  simp only [B0579.cell, cellLen, mem_prod, mem_Ico, mem_univ, and_true] at hy ⊢
  have e1 : Real.sqrt a * (c / Real.sqrt a / 2) = c / 2 := by field_simp
  have h1 := mul_le_mul_of_nonneg_left hy.1 hs.le
  have h2 := mul_lt_mul_of_pos_left hy.2 hs
  rw [mul_neg, e1] at h1
  rw [e1] at h2
  exact ⟨h1, h2⟩

/-- At the terminal age the moving adjoint is the moving datum, a.e. on the moving cell. -/
theorem movingPhi_terminal_ae {ν c m t s : ℝ} (hν : 0 < ν) (hs0 : 0 ≤ s)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {Γ : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointFlow ν c m tr t s (physAdj (clockA ν s) Γ) φ) :
    ∀ᵐ y ∂(volume.restrict (B0579.cell (cellLen c (clockA ν s)))), movingPhi ν φ s y = Γ y := by
  have ha : 0 < clockA ν s := by unfold clockA; positivity
  have hsq : 0 < Real.sqrt (clockA ν s) := Real.sqrt_pos.mpr ha
  have hT := hφ.terminal
  rw [Filter.EventuallyEq, ae_restrict_iff' (B0579.measurableSet_cell c)] at hT
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ × ℝ)) hsq.ne'
  have hT' := hq.ae hT
  rw [ae_restrict_iff' (B0579.measurableSet_cell _)]
  filter_upwards [hT'] with y hy hyc
  have e : Real.sqrt (clockA ν s) • y = (Real.sqrt (clockA ν s) * y.1,
      Real.sqrt (clockA ν s) * y.2) := by
    ext <;> simp [smul_eq_mul]
  rw [e] at hy
  have h := hy (mem_cell_scale ha hyc)
  unfold movingPhi
  rw [h]
  unfold physAdj
  have e1 : Real.sqrt (clockA ν s) * y.1 / Real.sqrt (clockA ν s) = y.1 := by field_simp
  have e2 : Real.sqrt (clockA ν s) * y.2 / Real.sqrt (clockA ν s) = y.2 := by field_simp
  rw [e1, e2, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ha.ne', Complex.ofReal_one,
    one_mul]

/-- `movCx` is `J_a⁻¹` of the complex combination. -/
theorem movCx_eq_JscaleInv (a : ℝ) (F₁ F₂ : B0579.Plane → ℝ) :
    movCx a F₁ F₂ = JscaleInv a (fun x => ((F₁ x : ℝ) : ℂ) + Complex.I * ((F₂ x : ℝ) : ℂ)) := by
  funext y; unfold movCx JscaleInv; ring

/-- Splitting a pairing of `F₁ + iF₂` (`F_k ∈ X_{m,c}` real) against `B ∈ X_{-m,c}`. -/
theorem pair_split {c m : ℝ} {F₁ F₂ : B0579.Plane → ℝ} {B : ℝ × ℝ → ℂ}
    (h₁ : MemLp F₁ 2 (B0579.cellMeasure c m)) (h₂ : MemLp F₂ 2 (B0579.cellMeasure c m))
    (hB : MemLp B 2 (B0579.cellMeasure c (-m))) :
    ∫ x in B0579.cell c, (((F₁ x : ℝ) : ℂ) + Complex.I * ((F₂ x : ℝ) : ℂ)) * B x =
      (∫ x in B0579.cell c, ((F₁ x : ℝ) : ℂ) * B x) +
        Complex.I * ∫ x in B0579.cell c, ((F₂ x : ℝ) : ℂ) * B x := by
  have h₁c : MemLp (fun x => ((F₁ x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) := h₁.ofReal
  have h₂c : MemLp (fun x => ((F₂ x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) := h₂.ofReal
  have i1 := (pair_bound h₁c hB).1
  have i2 := (pair_bound h₂c hB).1
  have h := integral_add i1 (i2.const_mul Complex.I)
  rw [integral_const_mul] at h
  refine Eq.trans ?_ h
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- **Assembly**: `FreeMovingDualityM` from the existence, cylinder-duality and density leaves. -/
theorem freeMovingDualityM_of (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) (hEx : FreeAdjExists ν m tr t₁ t₂) (hCyl : FreeCylDuality ν m tr t₁ t₂)
    (hDense : CylDataDense) : FreeMovingDualityM ν m tr t₁ t₂ := by
  intro hm hν ht₁ h12 htr U hU hMeas hAvail s₂ hs₂ Γ hΓ
  obtain ⟨φ, hφ⟩ := hEx hm hν ht₁ h12 htr s₂ hs₂ Γ hΓ
  refine ⟨movingPhi ν φ, ⟨φ, hφ, fun r _ => Filter.EventuallyEq.rfl⟩, ?_⟩
  intro s₁ hs₁ g hg
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hm0 : 0 ≤ m := by linarith
  have hs₁0 : 0 ≤ s₁ := ht₁.trans hs₁.1
  have hs₂0 : 0 ≤ s₂ := ht₁.trans hs₂.1
  have ha₁ : 1 ≤ clockA ν s₁ := by
    unfold clockA; nlinarith [mul_nonneg hν.le hs₁0]
  have ha₂ : 1 ≤ clockA ν s₂ := by
    unfold clockA; nlinarith [mul_nonneg hν.le hs₂0]
  have hs₁I : s₁ ∈ Icc t₁ t₂ := ⟨hs₁.1, hs₁.2.trans hs₂.2⟩
  -- the physical terminal datum lies in `X_{-m,c}`
  have hgT : MemLp (physAdj (clockA ν s₂) Γ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    (hφ.memX s₂ ⟨hs₂.1, le_rfl⟩).ae_eq
      ((B0579.cellMeasure_ac (ν ^ (-2 : ℝ)) (-m)).ae_le hφ.terminal)
  -- the moving adjoint at `s₁` lies in `X_{-m,d(s₁)}`
  have hΦ₁ : MemLp (movingPhi ν φ s₁) 2 (B0579.cellMeasure (dd ν s₁) (-m)) := by
    rcases eq_or_lt_of_le hs₁.2 with h | h
    · rw [h]
      have hae := (B0579.cellMeasure_ac (dd ν s₂) (-m)).ae_le
        (movingPhi_terminal_ae hν hs₂0 hφ)
      exact hΓ.ae_eq (Filter.EventuallyEq.symm hae)
    · have hcont : Continuous (φ s₁) := (hφ.smooth s₁ ⟨hs₁.1, h⟩).continuous
      exact mpScaleMemLp m (ν ^ (-2 : ℝ)) (clockA ν s₁) hc (by linarith) (clockA ν s₁)⁻¹ (φ s₁)
        hcont (hφ.memX s₁ hs₁)
  -- images under `U` lie in `X_{m,d(s₂)}`
  have hUm : ∀ h : ℝ × ℝ → ℂ, MemLp h 2 (B0579.cellMeasure (dd ν s₁) m) →
      MemLp (U s₂ s₁ h) 2 (B0579.cellMeasure (dd ν s₂) m) := fun h hh =>
    ⟨hMeas s₁ s₂ hs₁.1 hs₁.2 hs₂.2 h hh,
      lt_of_le_of_lt (hU.1 s₁ s₂ hs₁.1 hs₁.2 hs₂.2 h)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hh.2)⟩
  -- differences of the two pairings
  have hAdiff : ∀ h₁ h₂ : ℝ × ℝ → ℂ, MemLp h₁ 2 (B0579.cellMeasure (dd ν s₁) m) →
      MemLp h₂ 2 (B0579.cellMeasure (dd ν s₁) m) →
      (∫ y in B0579.cell (dd ν s₂), U s₂ s₁ h₁ y * Γ y) -
          ∫ y in B0579.cell (dd ν s₂), U s₂ s₁ h₂ y * Γ y =
        ∫ y in B0579.cell (dd ν s₂), U s₂ s₁ (h₁ - h₂) y * Γ y := by
    intro h₁ h₂ hh₁ hh₂
    have hlin := (hU.2.2.1 s₁ s₂ hs₁.1 hs₁.2 hs₂.2).1 h₂ (h₁ - h₂) hh₂ (hh₁.sub hh₂)
    have e : (fun y => h₂ y + (h₁ - h₂) y) = h₁ := by funext y; simp
    rw [e] at hlin
    have hlin' := (B0579.ac_cellMeasure (dd ν s₂) m).ae_le hlin
    have i2 := (pair_bound (hUm h₂ hh₂) hΓ).1
    have i3 := (pair_bound (hUm _ (hh₁.sub hh₂)) hΓ).1
    rw [sub_eq_iff_eq_add', ← integral_add i2 i3]
    refine integral_congr_ae ?_
    filter_upwards [hlin'] with y hy
    rw [hy, add_mul]
  have hBdiff : ∀ h₁ h₂ : ℝ × ℝ → ℂ, MemLp h₁ 2 (B0579.cellMeasure (dd ν s₁) m) →
      MemLp h₂ 2 (B0579.cellMeasure (dd ν s₁) m) →
      (∫ y in B0579.cell (dd ν s₁), h₁ y * movingPhi ν φ s₁ y) -
          ∫ y in B0579.cell (dd ν s₁), h₂ y * movingPhi ν φ s₁ y =
        ∫ y in B0579.cell (dd ν s₁), (h₁ - h₂) y * movingPhi ν φ s₁ y := by
    intro h₁ h₂ hh₁ hh₂
    rw [← integral_sub (pair_bound hh₁ hΦ₁).1 (pair_bound hh₂ hΦ₁).1]
    congr 1; funext y; simp [sub_mul]
  -- the identity on complex cylinder data
  have hcyl : ∀ f₁ f₂ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f₁ →
      B0579.IsCylTest (ν ^ (-2 : ℝ)) f₂ → ∀ ω₁ ω₂ : ℝ → B0579.Plane → ℝ,
      UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₁ ω₁ →
      UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₂ ω₂ →
      ∫ y in B0579.cell (dd ν s₂), U s₂ s₁ (movCx (clockA ν s₁) f₁ f₂) y * Γ y =
        ∫ y in B0579.cell (dd ν s₁), movCx (clockA ν s₁) f₁ f₂ y * movingPhi ν φ s₁ y := by
    intro f₁ f₂ hf₁ hf₂ ω₁ ω₂ hω₁ hω₂
    have hagree := hU.2.2.2.1 s₁ s₂ hs₁.1 hs₁.2 hs₂.2 f₁ f₂ hf₁ hf₂ ω₁ ω₂ hω₁ hω₂
    have hagree' := (B0579.ac_cellMeasure (dd ν s₂) m).ae_le hagree
    have step1 : ∫ y in B0579.cell (dd ν s₂), U s₂ s₁ (movCx (clockA ν s₁) f₁ f₂) y * Γ y =
        ∫ y in B0579.cell (dd ν s₂), movCx (clockA ν s₂) (ω₁ s₂) (ω₂ s₂) y * Γ y :=
      integral_congr_ae (by filter_upwards [hagree'] with y hy; rw [hy])
    have ha₁p : 0 < clockA ν s₁ := by linarith
    have ha₂p : 0 < clockA ν s₂ := by linarith
    have cov₂ := pairingCoV (ν ^ (-2 : ℝ)) (clockA ν s₂) hc ha₂p
      (fun x => ((ω₁ s₂ x : ℝ) : ℂ) + Complex.I * ((ω₂ s₂ x : ℝ) : ℂ)) Γ
    have cov₁ := pairingCoV (ν ^ (-2 : ℝ)) (clockA ν s₁) hc ha₁p
      (fun x => ((f₁ x : ℝ) : ℂ) + Complex.I * ((f₂ x : ℝ) : ℂ)) (movingPhi ν φ s₁)
    rw [← movCx_eq_JscaleInv] at cov₂ cov₁
    have hpa : (fun x => (((f₁ x : ℝ) : ℂ) + Complex.I * ((f₂ x : ℝ) : ℂ)) *
        physAdj (clockA ν s₁) (movingPhi ν φ s₁) x) =
        fun x => (((f₁ x : ℝ) : ℂ) + Complex.I * ((f₂ x : ℝ) : ℂ)) * φ s₁ x := by
      funext x; rw [physAdj_movingPhi hν hs₁0 φ x]
    have hφ₁ : MemLp (φ s₁) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := hφ.memX s₁ hs₁
    have hω₁m := hω₁.memX s₂ hs₁.2
    have hω₂m := hω₂.memX s₂ hs₁.2
    have d₁ := hCyl hm hν ht₁ h12 htr s₂ hs₂ _ φ hφ s₁ hs₁ f₁ hf₁ ω₁ hω₁
    have d₂ := hCyl hm hν ht₁ h12 htr s₂ hs₂ _ φ hφ s₁ hs₁ f₂ hf₂ ω₂ hω₂
    rw [step1, cov₂, cov₁, hpa, pair_split hω₁m hω₂m hgT,
      pair_split hω₁.memLp_initial hω₂.memLp_initial hφ₁, d₁, d₂]
  -- density
  set E : ℝ := Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set G : ℝ := (xNorm (dd ν s₂) (-m) Γ).toReal with hG
  set P : ℝ := (xNorm (dd ν s₁) (-m) (movingPhi ν φ s₁)).toReal with hP
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  set D : ℂ := (∫ y in B0579.cell (dd ν s₂), U s₂ s₁ g y * Γ y) -
    ∫ y in B0579.cell (dd ν s₁), g y * movingPhi ν φ s₁ y with hD
  have key : ∀ ε : ℝ, 0 < ε → ‖D‖ ≤ ε * (E * G + P) := by
    intro ε hε
    obtain ⟨f₁, f₂, hf₁, hf₂, hclose⟩ :=
      hDense (ν ^ (-2 : ℝ)) (clockA ν s₁) m hc ha₁ hm0 g hg ε hε
    obtain ⟨ω₁, hω₁⟩ := hAvail s₁ hs₁I f₁ hf₁
    obtain ⟨ω₂, hω₂⟩ := hAvail s₁ hs₁I f₂ hf₂
    have hh : MemLp (movCx (clockA ν s₁) f₁ f₂) 2 (B0579.cellMeasure (dd ν s₁) m) :=
      Leaf1Aux.memLp_movCx hm0 ha₁ hω₁.memLp_initial hω₂.memLp_initial
    have hgh := hg.sub hh
    have hDe : D = (∫ y in B0579.cell (dd ν s₂),
          U s₂ s₁ (g - movCx (clockA ν s₁) f₁ f₂) y * Γ y) -
        ∫ y in B0579.cell (dd ν s₁),
          (g - movCx (clockA ν s₁) f₁ f₂) y * movingPhi ν φ s₁ y := by
      rw [← hAdiff g _ hg hh, ← hBdiff g _ hg hh, hcyl f₁ f₂ hf₁ hf₂ ω₁ ω₂ hω₁ hω₂, hD]
      ring
    have b1 := (pair_bound (hUm _ hgh) hΓ).2
    have b2 := (pair_bound hgh hΦ₁).2
    have hxn : (xNorm (dd ν s₁) m (g - movCx (clockA ν s₁) f₁ f₂)).toReal ≤ ε :=
      ENNReal.toReal_le_of_le_ofReal hε.le hclose.le
    have hUn : (xNorm (dd ν s₂) m (U s₂ s₁ (g - movCx (clockA ν s₁) f₁ f₂))).toReal ≤
        E * (xNorm (dd ν s₁) m (g - movCx (clockA ν s₁) f₁ f₂)).toReal := by
      have hb := hU.1 s₁ s₂ hs₁.1 hs₁.2 hs₂.2 (g - movCx (clockA ν s₁) f₁ f₂)
      have := ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgh.2).ne hb
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hE0] at this
    rw [ENNReal.toReal_mul] at b1 b2
    have hxn0 : 0 ≤ (xNorm (dd ν s₁) m (g - movCx (clockA ν s₁) f₁ f₂)).toReal :=
      ENNReal.toReal_nonneg
    calc ‖D‖ ≤ ‖∫ y in B0579.cell (dd ν s₂),
            U s₂ s₁ (g - movCx (clockA ν s₁) f₁ f₂) y * Γ y‖ +
          ‖∫ y in B0579.cell (dd ν s₁),
            (g - movCx (clockA ν s₁) f₁ f₂) y * movingPhi ν φ s₁ y‖ := by
          rw [hDe]; exact norm_sub_le _ _
      _ ≤ (E * ε) * G + ε * P := by
          refine add_le_add (b1.trans ?_) (b2.trans ?_)
          · exact mul_le_mul_of_nonneg_right (hUn.trans
              (mul_le_mul_of_nonneg_left hxn hE0)) hG0
          · exact mul_le_mul_of_nonneg_right hxn hP0
      _ = ε * (E * G + P) := by ring
  have hK : 0 ≤ E * G + P := by positivity
  have hD0 : ‖D‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖D‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have h1 := key (‖D‖ / (2 * (E * G + P + 1))) (by positivity)
    have h2 : ‖D‖ / (2 * (E * G + P + 1)) * (E * G + P) < ‖D‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 hD0)

end Leaf2DualityNeeded

open Leaf2DualityNeeded in
/-- **Target** (SP 2937-2958): `FreeMovingDuality`, now that `IsFreeMovingPropagator` carries the
measurability clause. -/
theorem freeMovingDuality_of (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) (hEx : FreeAdjExists ν m tr t₁ t₂) (hCyl : FreeCylDuality ν m tr t₁ t₂)
    (hDense : CylDataDense) : FreeMovingDuality ν m tr t₁ t₂ := by
  intro hm hν ht₁ h12 htr U hU hAvail
  exact freeMovingDualityM_of ν m tr t₁ t₂ hEx hCyl hDense hm hν ht₁ h12 htr U hU hU.2.2.2.2 hAvail


end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
