import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2

/-!
# Leaf `PartII-b:T11/2/2/1` (`DualTestAdmissible`)

`ψ_L = φ(η/L) σ^{μ-1} χ(σ) H(s-σ, q, η)` is smooth (away from `σ ∈ tsupport χ ⊂ (0,s)` it vanishes
on an open set), `c`-periodic in `q` (the `q`-periodicity of `H` at the positive time `s - σ`),
and vanishes outside a box `σ ∈ [m, M]`, `|η| ≤ R L` (`φ` has compact support in `[-R, R]`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem dualPsi_eq_zero_of_chi (μ : ℂ) (χ φ : ℝ → ℝ) (H : Coord → ℝ) (s L : ℝ) (x : Coord)
    (h : χ x.1 = 0) : dualPsi μ χ φ H s L x = 0 := by
  simp [dualPsi, dualPsiInf, h]

theorem dualPsi_eq_zero_of_phi (μ : ℂ) (χ φ : ℝ → ℝ) (H : Coord → ℝ) (s L : ℝ) (x : Coord)
    (h : φ (x.2.2 / L) = 0) : dualPsi μ χ φ H s L x = 0 := by
  simp [dualPsi, h]

theorem contDiffAt_cpow_pos_aux (μ : ℂ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun u : ℝ => (u : ℂ) ^ (μ - 1)) t := by
  have hz : (t : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using ht
  have hlog : ContDiffAt ℝ ∞ (fun u : ℝ => Complex.log (u : ℂ)) t :=
    ((Complex.contDiffAt_log hz).restrict_scalars ℝ).comp t
      (Complex.ofRealCLM.contDiff.contDiffAt)
  have hmul : ContDiffAt ℝ ∞ (fun u : ℝ => Complex.log (u : ℂ) * (μ - 1)) t :=
    hlog.mul contDiffAt_const
  have hexp : ContDiffAt ℝ ∞ (fun u : ℝ => Complex.exp (Complex.log (u : ℂ) * (μ - 1))) t := by
    first
    | exact hmul.cexp
    | exact ((Complex.contDiff_exp).contDiffAt.restrict_scalars ℝ).comp t hmul
  apply hexp.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
  exact Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (ne_of_gt hu)) _

theorem contDiffAt_dualPsi_of_mem (μ : ℂ) (χ φ : ℝ → ℝ) (H : Coord → ℝ) (s L : ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hφ : ContDiff ℝ ∞ φ)
    (hH : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (x : Coord)
    (h0 : 0 < x.1) (hs : x.1 < s) :
    ContDiffAt ℝ ∞ (dualPsi μ χ φ H s L) x := by
  have hc : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hφL : ContDiffAt ℝ ∞ (fun y : Coord => (φ (y.2.2 / L) : ℂ)) x := by
    have h1 : ContDiff ℝ ∞ (fun y : Coord => y.2.2 / L) :=
      (contDiff_snd.comp contDiff_snd).div_const L
    exact (hc.comp (hφ.comp h1)).contDiffAt
  have hcpow : ContDiffAt ℝ ∞ (fun y : Coord => ((y.1 : ℂ)) ^ (μ - 1)) x :=
    (contDiffAt_cpow_pos_aux μ h0).comp x contDiff_fst.contDiffAt
  have hχx : ContDiffAt ℝ ∞ (fun y : Coord => (χ y.1 : ℂ)) x :=
    (hc.comp (hχ.comp contDiff_fst)).contDiffAt
  have hfg : ContDiff ℝ ∞ (fun y : Coord => (s - y.1, y.2)) :=
    (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hHa : ContDiffAt ℝ ∞ H (s - x.1, x.2) := by
    apply hH.contDiffAt
    apply IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ)
    exact ⟨show (0 : ℝ) < s - x.1 by linarith, mem_univ _⟩
  have hHx : ContDiffAt ℝ ∞ (fun y : Coord => (H (s - y.1, y.2) : ℂ)) x :=
    hc.contDiffAt.comp x (hHa.comp x hfg.contDiffAt)
  exact hφL.mul ((hcpow.mul hχx).mul hHx)

theorem dualPsi_qShift_aux (μ : ℂ) (χ φ : ℝ → ℝ) (H : Coord → ℝ) (s L : ℝ) (c ν r' : ℝ)
    (hχsupp : tsupport χ ⊆ Ioo (0 : ℝ) s) (hH : HeatSol c ν r' H) (x : Coord) :
    dualPsi μ χ φ H s L (qShift c x) = dualPsi μ χ φ H s L x := by
  by_cases hx : χ x.1 = 0
  · rw [dualPsi_eq_zero_of_chi μ χ φ H s L x hx,
      dualPsi_eq_zero_of_chi μ χ φ H s L (qShift c x) hx]
  · have hmem : x.1 ∈ tsupport χ := subset_tsupport χ (Function.mem_support.2 hx)
    have hxs := hχsupp hmem
    have hpos : 0 < s - x.1 := by linarith [hxs.2]
    have key : H (s - x.1, (x.2.1 + c, x.2.2)) = H (s - x.1, x.2) :=
      hH.periodic (s - x.1, x.2) hpos
    simp only [dualPsi, dualPsiInf, qShift]
    rw [key]

theorem dualPsi_support_aux (μ : ℂ) (χ φ : ℝ → ℝ) (H : Coord → ℝ) (s L : ℝ)
    (hχc : HasCompactSupport χ) (hχsupp : tsupport χ ⊆ Ioo (0 : ℝ) s)
    (hφc : HasCompactSupport φ) (hL : 0 < L) :
    ∃ σ Hh Lm : ℝ, 0 < σ ∧ ∀ x : Coord,
      (x.1 < σ ∨ Hh < x.1 ∨ Lm < |x.2.2|) → dualPsi μ χ φ H s L x = 0 := by
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  have hRφ : ∀ t : ℝ, R < |t| → φ t = 0 := by
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hR hmem
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at h1
    linarith
  have hK := hχc.isCompact
  rcases (tsupport χ).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, 0, R * L, one_pos, fun x _ =>
      dualPsi_eq_zero_of_chi μ χ φ H s L x (image_eq_zero_of_notMem_tsupport ?_)⟩
    simp [hE]
  · obtain ⟨m, hm, hmin⟩ := hK.exists_isMinOn hne continuousOn_id
    obtain ⟨M, hM, hmax⟩ := hK.exists_isMaxOn hne continuousOn_id
    have hmin' : ∀ y ∈ tsupport χ, m ≤ y := fun y hy => hmin hy
    have hmax' : ∀ y ∈ tsupport χ, y ≤ M := fun y hy => hmax hy
    refine ⟨m, M, R * L, (hχsupp hm).1, fun x hx => ?_⟩
    rcases hx with h | h | h
    · exact dualPsi_eq_zero_of_chi μ χ φ H s L x
        (image_eq_zero_of_notMem_tsupport (fun hy => absurd (hmin' _ hy) (not_le.2 h)))
    · exact dualPsi_eq_zero_of_chi μ χ φ H s L x
        (image_eq_zero_of_notMem_tsupport (fun hy => absurd (hmax' _ hy) (not_le.2 h)))
    · apply dualPsi_eq_zero_of_phi
      apply hRφ
      rw [abs_div, abs_of_pos hL]
      exact (lt_div_iff₀ hL).2 (by linarith)

end UnforcedLeray.Short.IIb

open UnforcedLeray.Short.IIb in
/-- Leaf `PartII-b:T11/2/2/1`: `ψ_L` is an admissible cell-stream test. -/
theorem DualTestAdmissible_proof : UnforcedLeray.Short.IIb.DualTestAdmissible := by
  intro c ν μ H s r' χ φ L hc hν hs hH hχ hφ hL
  obtain ⟨hχc, hχcs, hχsupp⟩ := hχ
  obtain ⟨hφc, hφcs, hφ0, hφ1⟩ := hφ
  refine ⟨?_, fun x => dualPsi_qShift_aux μ χ φ H s L c ν r' hχsupp hH x,
    dualPsi_support_aux μ χ φ H s L hχcs hχsupp hφcs hL⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x.1 ∈ tsupport χ
  · have hx' := hχsupp hx
    exact contDiffAt_dualPsi_of_mem μ χ φ H s L hχc hφc hH.smooth x hx'.1 hx'.2
  · have hopen : IsOpen ((fun y : Coord => y.1) ⁻¹' (tsupport χ)ᶜ) :=
      (isClosed_tsupport χ).isOpen_compl.preimage continuous_fst
    have hev : dualPsi μ χ φ H s L =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [hopen.mem_nhds (show x ∈ (fun y : Coord => y.1) ⁻¹' (tsupport χ)ᶜ from hx)]
        with y hy
      exact dualPsi_eq_zero_of_chi μ χ φ H s L y (image_eq_zero_of_notMem_tsupport hy)
    exact contDiffAt_const.congr_of_eventuallyEq hev
