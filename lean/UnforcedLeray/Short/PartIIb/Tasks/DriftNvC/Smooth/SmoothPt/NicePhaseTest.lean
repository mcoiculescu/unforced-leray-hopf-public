import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1_2

/-!
# `PartII-b:T08/1/2/1`: `N_v b` is a phase test for nice `b`

Source: `the November 2 reference manuscript` lines 1903-1915.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.Axi

namespace NicePT

theorem contDiff_reM : ContDiff ℝ ∞ (fun v : CMerid => reM v) := by
  unfold reM
  rw [contDiff_euclidean]
  intro i
  have h : ContDiff ℝ ∞ (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ)) :=
    ContinuousLinearMap.contDiff _
  exact Complex.reCLM.contDiff.comp h

theorem contDiff_imM : ContDiff ℝ ∞ (fun v : CMerid => imM v) := by
  unfold imM
  rw [contDiff_euclidean]
  intro i
  have h : ContDiff ℝ ∞ (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ)) :=
    ContinuousLinearMap.contDiff _
  exact Complex.imCLM.contDiff.comp h

theorem contDiff_realC : ContDiff ℝ ∞ (fun x : Space => realC x) := by
  unfold realC
  refine ContDiff.sum fun i _ => ?_
  have h : ContDiff ℝ ∞ (fun x : Space => ((x i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff
  exact h.smul contDiff_const

/-- Smoothness of the real ring lift of a profile vanishing for large `s`. -/
theorem contDiff_Nv {R : ℝ} (hR : 0 < R) {B : Coord → Merid} (hB : ContDiff ℝ ∞ B)
    {s1 : ℝ} (h1 : ∀ x : Coord, s1 < x.1 → B x = 0) :
    ContDiff ℝ ∞ (fun p : ℝ × Space => Nv R B p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  set S : ℝ := |s1| + 1 with hS
  have hSpos : 0 < S := by positivity
  set δ : ℝ := R / √S with hδ
  have hδpos : 0 < δ := div_pos hR (Real.sqrt_pos.2 hSpos)
  -- vanishing near the axis
  have hzero : ∀ q : ℝ × Space, ϱ q.2 < δ → Nv R B q.1 q.2 = 0 := by
    intro q hq
    by_cases h0 : ϱ q.2 = 0
    · have : age R q.2 = 0 := by simp [Axi.age, h0]
      simp [Nv, this]
    · have hpos : 0 < ϱ q.2 := lt_of_le_of_ne (ϱ_nonneg _) (Ne.symm h0)
      have hsq : ϱ q.2 * √S < R := by
        have := (lt_div_iff₀ (Real.sqrt_pos.2 hSpos)).1 hq
        exact this
      have hS' : S < age R q.2 := by
        unfold Axi.age
        rw [lt_div_iff₀ (by positivity)]
        have h2 : (ϱ q.2 * √S) ^ 2 < R ^ 2 := by
          exact pow_lt_pow_left₀ hsq (by positivity) (by norm_num)
        have : (ϱ q.2 * √S) ^ 2 = ϱ q.2 ^ 2 * S := by
          rw [mul_pow, Real.sq_sqrt hSpos.le]
        nlinarith
      have hs1 : s1 < (chart R q.1 q.2).1 := by
        show s1 < age R q.2
        have : s1 ≤ |s1| := le_abs_self _
        linarith
      simp [Nv, h1 _ hs1]
  by_cases hax : ϱ p.2 < δ
  · have hev : (fun q : ℝ × Space => Nv R B q.1 q.2) =ᶠ[𝓝 p] fun _ => (0 : Space) := by
      have hopen : IsOpen {q : ℝ × Space | ϱ q.2 < δ} :=
        isOpen_lt (continuous_ϱ.comp continuous_snd) continuous_const
      filter_upwards [hopen.mem_nhds hax] with q hq using hzero q hq
    exact (contDiffAt_const).congr_of_eventuallyEq hev
  · have hpos : 0 < ϱ p.2 := lt_of_lt_of_le hδpos (not_lt.1 hax)
    have hnax : p.2 ∉ axis := fun h => by
      have := (mem_axis_iff _).1 h; linarith
    have hopen : IsOpen {q : ℝ × Space | q.2 ∉ axis} :=
      isOpen_compl_axis.preimage continuous_snd
    refine ContDiffOn.contDiffAt ?_ (hopen.mem_nhds hnax)
    have hmaps : MapsTo (fun q : ℝ × Space => q.2) {q : ℝ × Space | q.2 ∉ axis} axisᶜ :=
      fun q hq => hq
    have hϱ : ContDiffOn ℝ ∞ (fun q : ℝ × Space => ϱ q.2) {q : ℝ × Space | q.2 ∉ axis} :=
      contDiffOn_ϱ.comp contDiff_snd.contDiffOn hmaps
    have hϱne : ∀ q ∈ {q : ℝ × Space | q.2 ∉ axis}, ϱ q.2 ≠ 0 := fun q hq => ϱ_ne_zero hq
    have hage : ContDiffOn ℝ ∞ (fun q : ℝ × Space => Axi.age R q.2)
        {q : ℝ × Space | q.2 ∉ axis} := by
      unfold Axi.age
      exact contDiffOn_const.div (hϱ.pow 2) fun q hq => pow_ne_zero 2 (hϱne q hq)
    have hagepos : ∀ q ∈ {q : ℝ × Space | q.2 ∉ axis}, Axi.age R q.2 ≠ 0 := fun q hq =>
      (Axi.age_pos hR.ne' hq).ne'
    have hsq : ContDiffOn ℝ ∞ (fun q : ℝ × Space => √(Axi.age R q.2))
        {q : ℝ × Space | q.2 ∉ axis} := hage.sqrt hagepos
    have hphase : ContDiffOn ℝ ∞ (fun q : ℝ × Space => Axi.phase R q.1 q.2)
        {q : ℝ × Space | q.2 ∉ axis} := by
      unfold Axi.phase
      exact ((contDiffOn_const.mul contDiff_fst.contDiffOn).div_const 2).sub
        ((contDiffOn_const.mul (hage.log hagepos)))
    have htrans : ContDiffOn ℝ ∞ (fun q : ℝ × Space => Axi.trans R q.2)
        {q : ℝ × Space | q.2 ∉ axis} := by
      unfold Axi.trans
      have h2 : ContDiff ℝ ∞ (fun q : ℝ × Space => q.2 2) :=
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
      exact (contDiffOn_const.mul h2.contDiffOn).div hϱ hϱne
    have hchart : ContDiffOn ℝ ∞ (fun q : ℝ × Space => Axi.chart R q.1 q.2)
        {q : ℝ × Space | q.2 ∉ axis} :=
      hage.prodMk (hphase.prodMk htrans)
    have hBc : ContDiffOn ℝ ∞ (fun q : ℝ × Space => B (Axi.chart R q.1 q.2))
        {q : ℝ × Space | q.2 ∉ axis} := hB.contDiffOn.comp hchart (fun _ _ => mem_univ _)
    have hB0 : ContDiffOn ℝ ∞ (fun q : ℝ × Space => B (Axi.chart R q.1 q.2) 0)
        {q : ℝ × Space | q.2 ∉ axis} :=
      (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hBc
    have hB1 : ContDiffOn ℝ ∞ (fun q : ℝ × Space => B (Axi.chart R q.1 q.2) 1)
        {q : ℝ × Space | q.2 ∉ axis} :=
      (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hBc
    have heR : ContDiffOn ℝ ∞ (fun q : ℝ × Space => eR q.2) {q : ℝ × Space | q.2 ∉ axis} :=
      contDiffOn_eR.comp contDiff_snd.contDiffOn hmaps
    have hfr : ContDiffOn ℝ ∞ (fun q : ℝ × Space => frameL q.2 (B (Axi.chart R q.1 q.2)))
        {q : ℝ × Space | q.2 ∉ axis} := by
      have : (fun q : ℝ × Space => frameL q.2 (B (Axi.chart R q.1 q.2))) =
          fun q => B (Axi.chart R q.1 q.2) 0 • eR q.2 + B (Axi.chart R q.1 q.2) 1 • e3 :=
        funext fun q => frameL_apply _ _
      rw [this]
      exact (hB0.smul heR).add (hB1.smul contDiffOn_const)
    exact hsq.smul hfr

theorem bounded_Nv {R : ℝ} (hR : 0 < R) {B : Coord → Merid} {s0 s1 L : ℝ} (hs0 : 0 < s0)
    (hz : ∀ x : Coord, (x.1 < s0 ∨ s1 < x.1 ∨ L < |x.2.2|) → B x = 0) :
    ∃ Rr : ℝ, ∀ (τ : ℝ) (y : Space), Rr < ‖y‖ → Nv R B τ y = 0 := by
  refine ⟨√((R ^ 2 / s0) * (1 + L ^ 2 / R ^ 2)), ?_⟩
  intro τ y hy
  by_contra hne
  have hB : B (chart R τ y) ≠ 0 := by
    intro h; apply hne; simp [Nv, h]
  have h1 : s0 ≤ age R y := by
    by_contra h; exact hB (hz _ (Or.inl (not_le.1 h)))
  have h2 : age R y ≤ s1 := by
    by_contra h; exact hB (hz _ (Or.inr (Or.inl (not_le.1 h))))
  have h3 : |trans R y| ≤ L := by
    by_contra h; exact hB (hz _ (Or.inr (Or.inr (not_le.1 h))))
  have hϱpos : 0 < ϱ y := by
    rcases (ϱ_nonneg y).lt_or_eq with h | h
    · exact h
    · exfalso
      have : age R y = 0 := by simp [Axi.age, ← h]
      linarith
  have hage : ϱ y ^ 2 * s0 ≤ R ^ 2 := by
    unfold Axi.age at h1
    rwa [le_div_iff₀ (by positivity), mul_comm] at h1
  have hϱ2 : ϱ y ^ 2 ≤ R ^ 2 / s0 := by
    rw [le_div_iff₀ hs0]; exact hage
  have htr : |y 2| ≤ L * ϱ y / R := by
    unfold Axi.trans at h3
    rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hϱpos, div_le_iff₀ hϱpos] at h3
    rw [le_div_iff₀ hR]; nlinarith
  have hy2 : y 2 ^ 2 ≤ L ^ 2 / R ^ 2 * ϱ y ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) htr 2
    rw [sq_abs, div_pow, mul_pow] at h
    calc y 2 ^ 2 ≤ L ^ 2 * ϱ y ^ 2 / R ^ 2 := h
      _ = _ := by ring
  have hnorm : ‖y‖ ^ 2 = ϱ y ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), ϱ_sq]
    simp [Fin.sum_univ_three]
  have hbd : ‖y‖ ^ 2 ≤ (R ^ 2 / s0) * (1 + L ^ 2 / R ^ 2) := by
    rw [hnorm]
    have : 0 ≤ L ^ 2 / R ^ 2 := by positivity
    nlinarith
  have := Real.sqrt_le_sqrt hbd
  rw [Real.sqrt_sq (norm_nonneg _)] at this
  linarith

theorem periodic_Nv {R c : ℝ} (hR : 0 < R) {B : Coord → Merid}
    (hper : ∀ x : Coord, B (x.1, (x.2.1 + c, x.2.2)) = B x) (τ : ℝ) (y : Space) :
    Nv R B (τ + 2 * c / R) y = Nv R B τ y := by
  have hph : Axi.phase R (τ + 2 * c / R) y = Axi.phase R τ y + c := by
    unfold Axi.phase
    field_simp
    ring
  have hch : Axi.chart R (τ + 2 * c / R) y = ((Axi.chart R τ y).1,
      ((Axi.chart R τ y).2.1 + c, (Axi.chart R τ y).2.2)) := by
    simp only [Axi.chart, hph]
  unfold Nv
  rw [hch, hper]

end NicePT

open NicePT in
theorem nvCNicePhaseTest_proof : UnforcedLeray.Short.IIb.NvCNicePhaseTest := by
  intro c ε b hc hε hb
  obtain ⟨hsm, hper, s0, s1, L, hs0, hz⟩ := hb
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hre : ContDiff ℝ ∞ (fun z => reM (b z)) := contDiff_reM.comp hsm
  have him : ContDiff ℝ ∞ (fun z => imM (b z)) := contDiff_imM.comp hsm
  have hzre : ∀ x : Coord, (x.1 < s0 ∨ s1 < x.1 ∨ L < |x.2.2|) → reM (b x) = 0 := by
    intro x hx; rw [hz x hx]; ext i; simp [reM]
  have hzim : ∀ x : Coord, (x.1 < s0 ∨ s1 < x.1 ∨ L < |x.2.2|) → imM (b x) = 0 := by
    intro x hx; rw [hz x hx]; ext i; simp [imM]
  have hpre : ∀ x : Coord, reM (b (x.1, (x.2.1 + c, x.2.2))) = reM (b x) := by
    intro x; have := hper x; simp only [qShift] at this; rw [this]
  have hpim : ∀ x : Coord, imM (b (x.1, (x.2.1 + c, x.2.2))) = imM (b x) := by
    intro x; have := hper x; simp only [qShift] at this; rw [this]
  have sre := contDiff_Nv hR hre (s1 := s1) (fun x hx => hzre x (Or.inr (Or.inl hx)))
  have sim := contDiff_Nv hR him (s1 := s1) (fun x hx => hzim x (Or.inr (Or.inl hx)))
  obtain ⟨R1, hR1⟩ := bounded_Nv hR hs0 hzre
  obtain ⟨R2, hR2⟩ := bounded_Nv hR hs0 hzim
  have hP : 2 * c / ε⁻¹ = 2 * ε * c := by field_simp
  refine ⟨?_, ?_, ⟨max R1 R2, ?_⟩⟩
  · unfold NvC
    exact (contDiff_realC.comp sre).add ((contDiff_realC.comp sim).const_smul Complex.I)
  · intro τ y
    unfold NvC
    have e1 := periodic_Nv (B := fun z => reM (b z)) (c := c) hR hpre τ y
    have e2 := periodic_Nv (B := fun z => imM (b z)) (c := c) hR hpim τ y
    rw [hP] at e1 e2
    simp only [e1, e2]
  · intro τ y hy
    unfold NvC
    rw [hR1 τ y (lt_of_le_of_lt (le_max_left _ _) hy), hR2 τ y (lt_of_le_of_lt (le_max_right _ _) hy)]
    simp [realC]

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.nvCNicePhaseTest_proof
