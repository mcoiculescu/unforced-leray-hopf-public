import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.Defs

/-!
# Measurability of a window Hessian (source 1437-1441)

Task `PartIII-b:C/ward/12/3/1/2/2/6`.  Hessian analogue of `PartII-a` `windowLapAEMeas`
(`Short/PartII-a/Tasks/F04aGlobalField/WindowLapAEMeas.lean`).  Only the integrability conjunct
of `IsWindowHess` is used: for a smooth compactly supported bump `g` in the window and each
component `c`, the field `g • e_c` is an admissible test, so `g · H_c` is integrable; dividing by
`g` gives `H_c` a.e. strongly measurable on `{g ≠ 0}`. Countably many such sets cover the window.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Parabolic (PS IsSTTest sD2)
open UnforcedLeray.Short.PartIIa (WindowCutoff windowField windowLap winSet)

theorem windowHessAEMeas : WindowHessAEMeas := by
  intro ν τ₀ j k W H hH
  have hWopen : IsOpen (winSet τ₀) := isOpen_Ioo.prod isOpen_univ
  -- on the support of a test bump, every component of `H` is a.e. strongly measurable
  have hcompM : ∀ g : ℝ × Space → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ winSet τ₀ → ∀ c : Fin 3,
        AEStronglyMeasurable (fun p => H p c) (volume.restrict (Function.support g)) := by
    intro g hgc hgcs hgS c
    obtain ⟨v, hv⟩ : ∃ v : CVec3, v = EuclideanSpace.single c 1 := ⟨_, rfl⟩
    have hψc : ContDiff ℝ ∞ (fun p : ℝ × Space => g p • v) := hgc.smul contDiff_const
    have hψcs : HasCompactSupport (fun p : ℝ × Space => g p • v) := hgcs.smul_right
    have hψS : tsupport (fun p : ℝ × Space => g p • v) ⊆
        Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) :=
      (tsupport_smul_subset_left g (fun _ : ℝ × Space => v)).trans hgS
    obtain ⟨_, hH2, _⟩ := hH (fun p => g p • v) hψc hψcs hψS
    have hcong : (fun p => dotL (H p) (g p • v)) = fun p => (g p : ℂ) * H p c := by
      funext p
      simp [hv, dotL_apply, EuclideanSpace.single_apply, Complex.real_smul]
    have hint : Integrable (fun p => (g p : ℂ) * H p c) := by
      rw [← hcong]
      exact hH2
    have hcont : Continuous g := hgc.continuous
    have hmeasinv : Measurable (fun p => (((g p)⁻¹ : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (measurable_inv.comp hcont.measurable)
    have hm1 : AEStronglyMeasurable (fun p => (((g p)⁻¹ : ℝ) : ℂ) * ((g p : ℂ) * H p c))
        (volume.restrict (Function.support g)) :=
      (hmeasinv.aestronglyMeasurable.mul hint.aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
    have hopen : IsOpen (Function.support g) := isOpen_ne_fun hcont continuous_const
    have heq : (fun p => (((g p)⁻¹ : ℝ) : ℂ) * ((g p : ℂ) * H p c))
        =ᵐ[volume.restrict (Function.support g)] (fun p => H p c) := by
      filter_upwards [ae_restrict_mem hopen.measurableSet] with p hp
      have hne : g p ≠ 0 := Function.mem_support.1 hp
      have key : (((g p)⁻¹ : ℝ) : ℂ) * ((g p : ℂ) * H p c) = H p c := by
        rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hne, Complex.ofReal_one, one_mul]
      exact key
    exact hm1.congr heq
  -- cover the window by countably many supports of bumps
  have hG : ∀ x : ℝ × Space, ∃ g : ℝ × Space → ℝ, x ∈ winSet τ₀ →
      (ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ winSet τ₀ ∧ g x ≠ 0) := by
    intro x
    by_cases hx : x ∈ winSet τ₀
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hWopen x hx
      let bump : ContDiffBump x :=
        { rIn := ε / 4, rOut := ε / 2, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
      refine ⟨⇑bump, fun _ => ⟨bump.contDiff, bump.hasCompactSupport, ?_, ?_⟩⟩
      · rw [bump.tsupport_eq]
        exact (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball
      · rw [bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)]
        norm_num
    · exact ⟨0, fun h => absurd h hx⟩
  choose G hG using hG
  have hcover := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => Function.support (G x)) (s := winSet τ₀) (fun x hx => by
      obtain ⟨hc, _, _, hne⟩ := hG x hx
      have hopen : IsOpen (Function.support (G x)) := isOpen_ne_fun hc.continuous continuous_const
      exact mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hne))
  obtain ⟨t, htS, htc, hsubt⟩ := hcover
  haveI : Countable t := htc.to_subtype
  have hsub : winSet τ₀ ⊆ ⋃ i : t, Function.support (G i.1) := by
    intro p hp
    obtain ⟨x, hxt, hpx⟩ := mem_iUnion₂.1 (hsubt hp)
    exact mem_iUnion.2 ⟨⟨x, hxt⟩, hpx⟩
  have hpieces : ∀ i : t, AEStronglyMeasurable H (volume.restrict (Function.support (G i.1))) := by
    intro i
    obtain ⟨hc, hcs, hcS, _⟩ := hG i.1 (htS i.2)
    have hcomps := fun c => hcompM (G i.1) hc hcs hcS c
    have hsum : H = fun p => H p 0 • EuclideanSpace.single 0 1 + H p 1 • EuclideanSpace.single 1 1
        + H p 2 • EuclideanSpace.single 2 1 := by
      funext p
      ext j
      fin_cases j <;> simp [EuclideanSpace.single_apply]
    rw [hsum]
    exact (((hcomps 0).smul_const _).add ((hcomps 1).smul_const _)).add ((hcomps 2).smul_const _)
  have hU : AEStronglyMeasurable H (volume.restrict (⋃ i : t, Function.support (G i.1))) :=
    aestronglyMeasurable_iUnion_iff.2 hpieces
  exact hU.mono_measure (Measure.restrict_mono hsub le_rfl)

end UnforcedLeray.Short.PartIIIb.Concrete
