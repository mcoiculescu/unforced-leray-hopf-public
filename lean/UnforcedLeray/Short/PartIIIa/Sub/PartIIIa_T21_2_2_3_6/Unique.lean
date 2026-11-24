import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6

/-!
# `PartIII-a:T21/2/2/3/6/1`: `AdjChiUnique` from five leaves

Source: `the November 2 reference manuscript` lines 2875-2896 (periodic kernel
`K_d`), 3052-3058 (adjoint localized interaction).  Proof of `AdjChiUnique`: kernel velocities
exist (`KernelBSExists`); both `χ`, `χ'` are band-integrable and so integrable against tests
(`BandMulTest`); `∫(χ-χ')ψ = 0` for all tests, so `χ = χ'` a.e. (`CellUnique`); the weak
derivative of `χ` is its classical one (`WeakDerivC1`), and weak derivatives agree
(`CellUnique` again).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- The band `{|η| ≤ R}` of the cell. -/
def bandSet (d R : ℝ) : Set (ℝ × ℝ) := B0579.cell d ∩ {x | |x.2| ≤ R}

/-- **Leaf K1** (SP 2875-2896): every cylinder test has a kernel Biot-Savart velocity
(periodic Biot-Savart kernel with mean-shear far field). -/
def KernelBSExists : Prop :=
  ∀ (d : ℝ) (ψ : ℝ × ℝ → ℝ), 0 < d → B0579.IsCylTest d ψ →
    ∃ u : ℝ × ℝ → Fin 2 → ℝ, IsKernelBiotSavart d ψ u

/-- **Leaf K2** (SP 3052-3058): a field with weak gradient `g'` and finite `H^1_{-m,d}` norm
is integrable on every band (a.e. measurability from the weak-derivative integrability against
tests, local `L^2` from the finite weighted norm and the weight being bounded below on bands). -/
def WeakFieldBandInt (m : ℝ) : Prop :=
  ∀ (d : ℝ) (χ' : ℝ × ℝ → ℂ) (g' : Fin 2 → ℝ × ℝ → ℂ), 0 < d →
    (∀ j, HasWeakCellDerivC d j χ' (g' j)) → h1Norm d m χ' g' ≠ ⊤ →
    ∀ R : ℝ, IntegrableOn χ' (bandSet d R) ∧ ∀ j, IntegrableOn (g' j) (bandSet d R)

/-- **Leaf K3** (du Bois-Reymond on the cylinder): a band-integrable field annihilated by all
cylinder tests vanishes a.e. on the cell. -/
def CellUnique : Prop :=
  ∀ (d : ℝ) (f : ℝ × ℝ → ℂ), 0 < d → (∀ R : ℝ, IntegrableOn f (bandSet d R)) →
    (∀ ψ, B0579.IsCylTest d ψ → ∫ x in B0579.cell d, f x * (ψ x : ℂ) = 0) →
    f =ᵐ[volume.restrict (B0579.cell d)] 0

/-- **Leaf K4**: a `C^1`, `d`-periodic field has its classical derivative as weak derivative on
the cylinder (integration by parts on the cell; seam terms cancel by periodicity). -/
def WeakDerivC1 : Prop :=
  ∀ (d : ℝ) (χ : ℝ × ℝ → ℂ), 0 < d → ContDiff ℝ 1 χ →
    (∀ y : ℝ × ℝ, χ (y.1 + d, y.2) = χ y) → ∀ j : Fin 2, HasWeakCellDerivC d j χ (pdCx j χ)

/-- **Leaf K5**: a band-integrable field is integrable against every cylinder test on the cell
(tests are bounded and vanish outside a band). -/
def BandMulTest : Prop :=
  ∀ (d : ℝ) (f : ℝ × ℝ → ℂ) (ψ : ℝ × ℝ → ℝ), 0 < d → (∀ R : ℝ, IntegrableOn f (bandSet d R)) →
    B0579.IsCylTest d ψ → IntegrableOn (fun x => f x * (ψ x : ℂ)) (B0579.cell d)

theorem continuous_bandInt {d : ℝ} {f : ℝ × ℝ → ℂ} (hf : Continuous f) (R : ℝ) :
    IntegrableOn f (bandSet d R) := by
  have hc : IsCompact (Icc (-(d / 2)) (d / 2) ×ˢ Icc (-R) R : Set (ℝ × ℝ)) :=
    isCompact_Icc.prod isCompact_Icc
  refine (hf.continuousOn.integrableOn_compact hc).mono_set ?_
  rintro ⟨a, b⟩ ⟨⟨⟨h1, h2⟩, _⟩, h3⟩
  exact ⟨⟨h1, h2.le⟩, abs_le.1 h3⟩

theorem int_sub_mul (d : ℝ) (f g : ℝ × ℝ → ℂ) (ψ : ℝ × ℝ → ℝ)
    (hf : IntegrableOn (fun x => f x * (ψ x : ℂ)) (B0579.cell d))
    (hg : IntegrableOn (fun x => g x * (ψ x : ℂ)) (B0579.cell d)) :
    ∫ x in B0579.cell d, (f - g) x * (ψ x : ℂ) =
      (∫ x in B0579.cell d, f x * (ψ x : ℂ)) - ∫ x in B0579.cell d, g x * (ψ x : ℂ) := by
  rw [← integral_sub hf hg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sub_mul]

theorem adjChiUnique_of (m : ℝ) (k1 : KernelBSExists) (k2 : WeakFieldBandInt m)
    (k3 : CellUnique) (k4 : WeakDerivC1) (k5 : BandMulTest) : AdjChiUnique m := by
  intro d E Φ χ χ' g' hd hΦ hχ1 hχp hχc hχ'c hw hne
  have hχcont : Continuous χ := hχ1.continuous
  obtain hband := k2 d χ' g' hd hw hne
  have hχb : ∀ R : ℝ, IntegrableOn χ (bandSet d R) := fun R => continuous_bandInt hχcont R
  have hχ'b : ∀ R : ℝ, IntegrableOn χ' (bandSet d R) := fun R => (hband R).1
  -- χ = χ' a.e.
  have hae : χ =ᵐ[volume.restrict (B0579.cell d)] χ' := by
    have hsub : (χ - χ') =ᵐ[volume.restrict (B0579.cell d)] 0 := by
      refine k3 d (χ - χ') hd (fun R => (hχb R).sub (hχ'b R)) ?_
      intro ψ hψ
      obtain ⟨u, hu⟩ := k1 d ψ hd hψ
      have e1 := hχc ψ u hψ hu
      have e2 := hχ'c ψ u hψ hu
      have i1 := k5 d χ ψ hd hχb hψ
      have i2 := k5 d χ' ψ hd hχ'b hψ
      have : ∫ x in B0579.cell d, (χ - χ') x * (ψ x : ℂ) =
          (∫ x in B0579.cell d, χ x * (ψ x : ℂ)) - ∫ x in B0579.cell d, χ' x * (ψ x : ℂ) :=
        int_sub_mul d χ χ' ψ i1 i2
      rw [this]
      exact sub_eq_zero.2 (e1.trans e2.symm)
    filter_upwards [hsub] with x hx
    exact sub_eq_zero.1 hx
  intro j
  have hχw := k4 d χ hd hχ1 hχp j
  have hdiff : (pdCx j χ - g' j) =ᵐ[volume.restrict (B0579.cell d)] 0 := by
    refine k3 d _ hd (fun R => (continuous_bandInt ?_ R).sub ((hband R).2 j)) ?_
    · have h1 : Continuous (fderiv ℝ χ) :=
        (contDiff_one_iff_fderiv.1 hχ1).2
      unfold pdCx
      exact h1.clm_apply continuous_const
    intro ψ hψ
    have a1 := hχw.1 ψ hψ
    have a2 := (hw j).1 ψ hψ
    have b1 := hχw.2 ψ hψ
    have b2 := (hw j).2 ψ hψ
    have hc : ∫ x in B0579.cell d, χ x * (B0579.pd j ψ x : ℂ) =
        ∫ x in B0579.cell d, χ' x * (B0579.pd j ψ x : ℂ) :=
      integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
    have : ∫ x in B0579.cell d, (pdCx j χ - g' j) x * (ψ x : ℂ) =
        (∫ x in B0579.cell d, pdCx j χ x * (ψ x : ℂ)) - ∫ x in B0579.cell d, g' j x * (ψ x : ℂ) :=
      int_sub_mul d _ _ ψ a1.2 a2.2
    rw [this]
    have b1' : ∫ x in B0579.cell d, χ x * (B0579.pd j ψ x : ℂ) =
        -∫ x in B0579.cell d, pdCx j χ x * (ψ x : ℂ) := b1
    have b2' : ∫ x in B0579.cell d, χ' x * (B0579.pd j ψ x : ℂ) =
        -∫ x in B0579.cell d, g' j x * (ψ x : ℂ) := b2
    linear_combination b1' - b2' - hc
  filter_upwards [hdiff] with x hx
  exact sub_eq_zero.1 hx

end UnforcedLeray.Short.IIIa.AdjE1

#print axioms UnforcedLeray.Short.IIIa.AdjE1.adjChiUnique_of
