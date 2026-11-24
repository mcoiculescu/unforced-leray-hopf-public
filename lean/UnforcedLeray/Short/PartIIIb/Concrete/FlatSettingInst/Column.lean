import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Setting
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Lin

/-!
# Zero-entrance forced columns of the flat equation (source 3420-3446, 4610-4615, 4761-4763)

Source of record: `the November 2 reference manuscript` (73 pages).

`𝔗_{μ,ν}A` is "the complete flat stress of the zero-entrance forced column with Gaussian age force
`f_{B_{μ,ν}[A]}`" (4761-4763): the column `b` solves
`∂_s b + (μ/s)b - νΔb + P₀div(v⊗b + b⊗v) = P₀f` (`P₀` the cylinder Leray projection, `v` the actual
train) in the zero-entrance energy class of `prop:short-polynomial-causal` (3420-3440).  The class
`IIIa.IsCausalEnergySolution` has a tensor force `P₀ div F`; the forced column has a body force `f`,
tested against divergence-free tests (so `P₀` is implicit, as in `IIIa.flatIntegrand`):

* `IsEnergyField c b G` : the six energy-class clauses of `IsCausalEnergySolution` (measurability,
  `b, ∇b ∈ L²_loc`, `b ∈ 𝓗` near `s = 0`, divergence free, `G` the weak gradient at every `s > 0`);
* `forcedIntegrand`, `IsForcedColumn` : the tested forced equation;
* `forcedColumn_sub` : the difference of two forced columns with the same force is a homogeneous
  causal energy solution (`F = 0`); `forcedColumn_unique` : so forced columns are unique when the
  homogeneous solutions vanish (`FlatHomogeneousUnique`, source 3541-3545).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest vnorm2 tnorm2
  HasWeakCellDerivC flatDt flatLap flatGrad)

/-- The energy class of `prop:short-polynomial-causal` (source 3426-3430): the clauses of
`IIIa.IsCausalEnergySolution` other than the equation. -/
structure IsEnergyField (c : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop where
  measurable : ∀ i, Measurable fun p => b p i
  gradMeasurable : ∀ i j, Measurable fun p => G p i j
  energyLoc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤
  zeroEntrance : ∃ δ : ℝ, 0 < δ ∧ ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
    ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤
  divFree : ∀ s, 0 < s → ∀ ψ, B0579.IsCylTest c ψ →
    ∫ x in B0579.cell c, (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0
  weakGrad : ∀ s, 0 < s → ∀ i j,
    HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j)

/-- The tested forced equation `∂_s b + (μ/s)b - νΔb + P₀div(v⊗b + b⊗v) = P₀f` against a
divergence-free test `Φ`: `-⟨b,Φ_s⟩ + (μ/s)⟨b,Φ⟩ - ν⟨b,ΔΦ⟩ - ⟨v⊗b+b⊗v, ∇Φ⟩ - ⟨f,Φ⟩` (bilinear
pairings, as in `IIIa.flatIntegrand` with `F = 0`). -/
def forcedIntegrand (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  flatIntegrand ν μ vel (fun _ _ _ => 0) b Φ p - ∑ i : Fin 2, f p i * (Φ p.1 p.2 i : ℂ)

/-- **A zero-entrance forced column** (source 3420-3440 with a body force; 4610-4615 "this causal
column has finite-energy entrance"; 4761-4763 "the zero-entrance forced column"). -/
structure IsForcedColumn (c ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop extends IsEnergyField c b G where
  integrable : ∀ Φ, IsFlatTest c Φ →
    IntegrableOn (forcedIntegrand ν μ vel f b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c)
  weak : ∀ Φ, IsFlatTest c Φ →
    ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, forcedIntegrand ν μ vel f b Φ p = 0

/-- The energy class of a causal energy solution. -/
theorem _root_.UnforcedLeray.Short.IIIa.IsCausalEnergySolution.toEnergyField {c ν : ℝ} {μ : ℂ}
    {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (h : IsCausalEnergySolution c ν μ vel F b G) : IsEnergyField c b G :=
  ⟨h.measurable, h.gradMeasurable, h.energyLoc, h.zeroEntrance, h.divFree, h.weakGrad⟩

/-- **The energy class is a real vector space** (the energy clauses of `IIIa.causalSolSub`,
source 3541-3545: "a homogeneous difference in the energy class"). -/
theorem IsEnergyField.sub {c : ℝ} {b b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G G' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hb : IsEnergyField c b G)
    (hb' : IsEnergyField c b' G') :
    IsEnergyField c (fun p i => b p i - b' p i) (fun p i j => G p i j - G' p i j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hb.measurable i).sub (hb'.measurable i)
  · intro i j
    exact (hb.gradMeasurable i j).sub (hb'.gradMeasurable i j)
  · intro s₁ s₂ h₁ h₂
    have hI := hb.energyLoc s₁ s₂ h₁ h₂
    have hI' := hb'.energyLoc s₁ s₂ h₁ h₂
    have hX : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2 :=
      ((IIIa.causalLin_measurable_vnorm2 hb.measurable).pow_const 2).add
        ((IIIa.causalLin_measurable_tnorm2 hb.gradMeasurable).pow_const 2)
    have hD : ∀ p : ℝ × (ℝ × ℝ),
        vnorm2 (fun i => b p i - b' p i) ^ 2 + tnorm2 (fun i j => G p i j - G' p i j) ^ 2 ≤
          2 * (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) +
            2 * (vnorm2 (b' p) ^ 2 + tnorm2 (G' p) ^ 2) := fun p => by
      linarith [IIIa.causalLin_vnorm2_sub_sq_le (b p) (b' p),
        IIIa.causalLin_tnorm2_sub_sq_le (G p) (G' p)]
    have key := IIIa.causalLin_lintegral_le (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) hX hD
    exact lt_of_le_of_lt key (by finiteness)
  · obtain ⟨δ₁, hδ₁, hI₁⟩ := hb.zeroEntrance
    obtain ⟨δ₂, hδ₂, hI₂⟩ := hb'.zeroEntrance
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    have hsub₁ : Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ (univ : Set (ℝ × ℝ)) ⊆
        Ioo (0 : ℝ) δ₁ ×ˢ (univ : Set (ℝ × ℝ)) :=
      prod_mono (Ioo_subset_Ioo_right (min_le_left _ _)) Subset.rfl
    have hsub₂ : Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ (univ : Set (ℝ × ℝ)) ⊆
        Ioo (0 : ℝ) δ₂ ×ˢ (univ : Set (ℝ × ℝ)) :=
      prod_mono (Ioo_subset_Ioo_right (min_le_right _ _)) Subset.rfl
    have hfin₁ : ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ univ)) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono' (Measure.restrict_mono hsub₁ le_rfl) le_rfl) hI₁
    have hfin₂ : ∫⁻ p, ENNReal.ofReal (vnorm2 (b' p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ univ)) < ⊤ :=
      lt_of_le_of_lt (lintegral_mono' (Measure.restrict_mono hsub₂ le_rfl) le_rfl) hI₂
    have hXb : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) ^ 2 :=
      (IIIa.causalLin_measurable_vnorm2 hb.measurable).pow_const 2
    have hD0 : ∀ p : ℝ × (ℝ × ℝ),
        vnorm2 (fun i => b p i - b' p i) ^ 2 ≤ 2 * vnorm2 (b p) ^ 2 + 2 * vnorm2 (b' p) ^ 2 :=
      fun p => IIIa.causalLin_vnorm2_sub_sq_le (b p) (b' p)
    have key := IIIa.causalLin_lintegral_le
      ((ageμ c (-3 / 2)).restrict (Ioo (0 : ℝ) (min δ₁ δ₂) ×ˢ univ)) hXb hD0
    exact lt_of_le_of_lt key (by finiteness)
  · intro s hs ψ hψ
    have h0 := hb.divFree s hs ψ hψ
    have h0' := hb'.divFree s hs ψ hψ
    have I0 : IntegrableOn (fun x => b (s, x) 0 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
      ((hb.weakGrad s hs 0 0).1 ψ hψ).1
    have I1 : IntegrableOn (fun x => b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
      ((hb.weakGrad s hs 1 1).1 ψ hψ).1
    have J0 : IntegrableOn (fun x => b' (s, x) 0 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell c) :=
      ((hb'.weakGrad s hs 0 0).1 ψ hψ).1
    have J1 : IntegrableOn (fun x => b' (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) :=
      ((hb'.weakGrad s hs 1 1).1 ψ hψ).1
    show ∫ x in B0579.cell c, ((b (s, x) 0 - b' (s, x) 0) * (B0579.pd 0 ψ x : ℂ) +
      (b (s, x) 1 - b' (s, x) 1) * (B0579.pd 1 ψ x : ℂ)) = 0
    have eqfun : (fun x => (b (s, x) 0 - b' (s, x) 0) * (B0579.pd 0 ψ x : ℂ) +
        (b (s, x) 1 - b' (s, x) 1) * (B0579.pd 1 ψ x : ℂ)) =
        fun x => (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) -
          (b' (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b' (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) := by
      funext x
      ring
    have hI : IntegrableOn (fun x => b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
        b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) := Integrable.add I0 I1
    have hJ : IntegrableOn (fun x => b' (s, x) 0 * (B0579.pd 0 ψ x : ℂ) +
        b' (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell c) := Integrable.add J0 J1
    rw [eqfun, integral_sub hI hJ, h0, h0', sub_self]
  · intro s hs i j
    have hE := hb.weakGrad s hs i j
    have hE' := hb'.weakGrad s hs i j
    unfold HasWeakCellDerivC at hE hE' ⊢
    refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
    · have e : (fun x => (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ)) =
          fun x => b (s, x) i * (B0579.pd j ψ x : ℂ) - b' (s, x) i * (B0579.pd j ψ x : ℂ) := by
        funext x
        ring
      show IntegrableOn (fun x => (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ))
        (B0579.cell c)
      rw [e]
      exact Integrable.sub (hE.1 ψ hψ).1 (hE'.1 ψ hψ).1
    · have e : (fun x => (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ)) =
          fun x => G (s, x) i j * (ψ x : ℂ) - G' (s, x) i j * (ψ x : ℂ) := by
        funext x
        ring
      show IntegrableOn (fun x => (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ)) (B0579.cell c)
      rw [e]
      exact Integrable.sub (hE.1 ψ hψ).2 (hE'.1 ψ hψ).2
    · have hA1 := (hE.1 ψ hψ).1
      have hB1 := (hE'.1 ψ hψ).1
      have hA2 := (hE.1 ψ hψ).2
      have hB2 := (hE'.1 ψ hψ).2
      have eq1 := hE.2 ψ hψ
      have eq2 := hE'.2 ψ hψ
      have eA : ∫ x in B0579.cell c, (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ) =
          (∫ x in B0579.cell c, b (s, x) i * (B0579.pd j ψ x : ℂ)) -
            ∫ x in B0579.cell c, b' (s, x) i * (B0579.pd j ψ x : ℂ) := by
        rw [← integral_sub hA1 hB1]
        congr 1
        funext x
        ring
      have eB : ∫ x in B0579.cell c, (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ) =
          (∫ x in B0579.cell c, G (s, x) i j * (ψ x : ℂ)) -
            ∫ x in B0579.cell c, G' (s, x) i j * (ψ x : ℂ) := by
        rw [← integral_sub hA2 hB2]
        congr 1
        funext x
        ring
      show ∫ x in B0579.cell c, (b (s, x) i - b' (s, x) i) * (B0579.pd j ψ x : ℂ) =
        -∫ x in B0579.cell c, (G (s, x) i j - G' (s, x) i j) * (ψ x : ℂ)
      linear_combination eA + eB + eq1 - eq2

/-- The forced integrand of a difference. -/
theorem forcedIntegrand_sub (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (b b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) :
    flatIntegrand ν μ vel (fun _ _ _ => 0) (fun p i => b p i - b' p i) Φ p =
      forcedIntegrand ν μ vel f b Φ p - forcedIntegrand ν μ vel f b' Φ p := by
  have h := IIIa.causalLin_flatIntegrand_sub ν μ vel (fun _ _ _ => 0) (fun _ _ _ => 0) b b' Φ p
  have e : (fun (_ : ℝ × (ℝ × ℝ)) (_ _ : Fin 2) => (0 : ℂ) - 0) = fun _ _ _ => 0 := by
    funext _ _ _
    exact sub_self 0
  rw [e] at h
  rw [h, forcedIntegrand, forcedIntegrand]
  ring

/-- **The difference of two forced columns with the same force is a homogeneous causal energy
solution** (source 3541-3545). -/
theorem forcedColumn_sub {c ν : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {b b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G G' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hb : IsForcedColumn c ν μ vel f b G)
    (hb' : IsForcedColumn c ν μ vel f b' G') :
    IsCausalEnergySolution c ν μ vel (fun _ _ _ => 0) (fun p i => b p i - b' p i)
      (fun p i j => G p i j - G' p i j) := by
  have hE := hb.toIsEnergyField.sub hb'.toIsEnergyField
  have hfun : ∀ Φ, flatIntegrand ν μ vel (fun _ _ _ => 0) (fun p i => b p i - b' p i) Φ =
      fun p => forcedIntegrand ν μ vel f b Φ p - forcedIntegrand ν μ vel f b' Φ p :=
    fun Φ => funext fun p => forcedIntegrand_sub ν μ vel f b b' Φ p
  refine ⟨hE.measurable, hE.gradMeasurable, hE.energyLoc, hE.zeroEntrance, hE.divFree,
    hE.weakGrad, fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
  · rw [hfun Φ]
    exact (hb.integrable Φ hΦ).sub (hb'.integrable Φ hΦ)
  · rw [hfun Φ, integral_sub (hb.integrable Φ hΦ) (hb'.integrable Φ hΦ), hb.weak Φ hΦ,
      hb'.weak Φ hΦ, sub_self]

/-- **Uniqueness of homogeneous causal energy solutions** at one regime (source 3541-3545:
"a homogeneous difference in the energy class ... apply `eq:short-causal-tail-energy` on
`[δ_j, B]` and let `j → ∞`"): every causal zero-entrance energy solution of the homogeneous
equation (`F = 0`) vanishes almost everywhere on `(0,∞) × cell`. -/
def FlatHomogeneousUnique (c ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ) : Prop :=
  ∀ (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    IsCausalEnergySolution c ν μ vel (fun _ _ _ => 0) b G →
      ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)), b p = 0

/-- **Forced columns are unique** (source 3426, 3541-3545). -/
theorem forcedColumn_unique {c ν : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    (hU : FlatHomogeneousUnique c ν μ vel) {f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {b b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G G' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hb : IsForcedColumn c ν μ vel f b G) (hb' : IsForcedColumn c ν μ vel f b' G') :
    b =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)] b' := by
  filter_upwards [hU _ _ (forcedColumn_sub hb hb')] with p hp
  funext i
  have := congrFun hp i
  simpa [sub_eq_zero] using this

/-- The zero field is a causal energy solution of the homogeneous equation. -/
theorem isCausal_zero (c ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ) :
    IsCausalEnergySolution c ν μ vel (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) := by
  have hv : vnorm2 (fun _ : Fin 2 => (0 : ℂ)) = 0 := by simp [vnorm2]
  have ht : tnorm2 (fun _ _ : Fin 2 => (0 : ℂ)) = 0 := by simp [tnorm2]
  have hF : ∀ Φ, flatIntegrand ν μ vel (fun _ _ _ => 0) (fun _ _ => 0) Φ = fun _ => 0 := by
    intro Φ
    funext p
    simp [flatIntegrand]
  refine ⟨fun i => measurable_const, fun i j => measurable_const, fun s₁ s₂ _ _ => ?_,
    ⟨1, one_pos, ?_⟩, fun s _ ψ _ => by simp, fun s _ i j => ?_, fun Φ _ => ?_, fun Φ _ => ?_⟩
  · simp [hv, ht]
  · simp [hv]
  · refine ⟨fun ψ _ => ⟨?_, ?_⟩, fun ψ _ => by simp⟩ <;> simp
  · rw [hF]
    exact integrableOn_zero
  · rw [hF]
    simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
