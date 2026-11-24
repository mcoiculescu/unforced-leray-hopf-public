import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

theorem t0g_iter_zero_of_notMem {Φ : Profile → ℝ} {p : Profile} (hp : p ∉ tsupport Φ) (k : ℕ) :
    iteratedFDeriv ℝ k Φ p = 0 := by
  have hev : Φ =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    have : (tsupport Φ)ᶜ ∈ 𝓝 p := (isClosed_tsupport Φ).isOpen_compl.mem_nhds hp
    filter_upwards [this] with q hq
    exact image_eq_zero_of_notMem_tsupport hq
  have h := (Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds
  rw [h]
  simp

theorem t0g_iter_periodic {c : ℝ} {Φ : Profile → ℝ} (hΦ : IsProfileTest c Φ) (k : ℕ) :
    QPeriodic c (iteratedFDeriv ℝ k Φ) := by
  intro p
  have hfun : (fun x : Profile => Φ (x + ((0 : ℝ), c, (0 : ℝ)))) = Φ := by
    funext x
    have hx : x + ((0 : ℝ), c, (0 : ℝ)) = (x.1, x.2.1 + c, x.2.2) := by
      ext <;> simp
    rw [hx]
    exact hΦ.periodic x
  have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := Φ) k ((0 : ℝ), c, (0 : ℝ)) p
  rw [hfun] at h
  have hp : p + ((0 : ℝ), c, (0 : ℝ)) = (p.1, p.2.1 + c, p.2.2) := by
    ext <;> simp
  rw [hp] at h
  exact h.symm

theorem t0gBdd_proof : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gBdd := by
  intro c hc Φ hΦ k
  obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
  set D : Profile → _ := iteratedFDeriv ℝ k Φ with hD
  have hcont : Continuous D := hΦ.smooth.continuous_iteratedFDeriv (by simp)
  have hper := t0g_iter_periodic hΦ k
  let K : Set Profile := Icc s0 s1 ×ˢ Icc (0 : ℝ) c ×ˢ Icc (-L) L
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, fun p => ?_⟩
  by_cases hp : p ∈ tsupport Φ
  · have hband := UnforcedLeray.B0226.tsupport_subset_band hb hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hband
    have hL := abs_le.1 h3
    set n : ℤ := ⌊p.2.1 / c⌋ with hn
    have hq0 : 0 ≤ p.2.1 - n * c := by
      have := Int.floor_le (p.2.1 / c)
      rw [le_div_iff₀ hc] at this
      linarith
    have hq1 : p.2.1 - n * c ≤ c := by
      have := Int.lt_floor_add_one (p.2.1 / c)
      rw [div_lt_iff₀ hc] at this
      linarith
    have hpf : Function.Periodic (fun q : ℝ => D (p.1, q, p.2.2)) c := fun q => hper (p.1, q, p.2.2)
    have heq : D (p.1, p.2.1 - n * c, p.2.2) = D p := hpf.sub_int_mul_eq n
    have hmem : (p.1, p.2.1 - n * c, p.2.2) ∈ K := ⟨⟨h1, h2⟩, ⟨hq0, hq1⟩, hL.1, hL.2⟩
    have := hC _ hmem
    rw [heq] at this
    exact this.trans (le_max_left _ _)
  · have h0 : D p = 0 := t0g_iter_zero_of_notMem hp k
    rw [h0]
    simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
