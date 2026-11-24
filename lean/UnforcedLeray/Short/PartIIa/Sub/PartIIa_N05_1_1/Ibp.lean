import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.Weak

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1_1P

theorem inner_rsmul_left (r : ℝ) (x y : MeridC) :
    inner ℂ (r • x) y = (r : ℂ) * inner ℂ x y := by simp
theorem inner_rsmul_right (r : ℝ) (x y : MeridC) :
    inner ℂ x (r • y) = (r : ℂ) * inner ℂ x y := by simp

theorem ibp_s {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {w Sw : HSpace c MeridC} (hS : N05_1_1Org.WeakS c w Sw) {φ : Profile → MeridC}
    (hφ : IsMeridTest c φ) :
    ∫ p, inner ℂ (dsFromS (fun p => cutRep c χ Sw p + cutRep c (fun p => p.1 * pdS χ p) w p) p)
        (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (cutRep c χ w p) (pdS φ p) ∂(cellMeasure c) := by
  have hSP := SP.of_cutoff hχ
  have hψ : IsMeridTest c (fun p => χ p • φ p) := mt_smul hSP hφ
  have h2 : IsMeridTest c (fun p => pdS χ p • φ p) := mt_smul hSP.pdS hφ
  have h3 : IsMeridTest c (fun p => χ p • pdS φ p) := mt_smul hSP (mt_pdS hφ)
  have hweak := weakS_lam hS hψ
  have hprod : pdS (fun p => χ p • φ p) = fun p => χ p • pdS φ p + pdS χ p • φ p :=
    funext (pdS_smul hχ.smooth hφ.smooth)
  rw [hprod, Lam_add hc w (nice_of_mt hc h3) (nice_of_mt hc h2)] at hweak
  have hL : ∫ p, inner ℂ (dsFromS (fun p => cutRep c χ Sw p +
        cutRep c (fun p => p.1 * pdS χ p) w p) p) (φ p) ∂(cellMeasure c) =
      Lam c Sw (fun p => p.1⁻¹ • (χ p • φ p)) + Lam c w (fun p => pdS χ p • φ p) := by
    unfold Lam
    rw [← integral_add (integrable_inner_periodize hc Sw (nice_sinv hc (nice_of_mt hc hψ)))
      (integrable_inner_periodize hc w (nice_of_mt hc h2))]
    unfold cellMeasure
    refine setIntegral_congr_fun (measurableSet_cell c) (fun p hp => ?_)
    have hp1 : 0 < p.1 := hp.1
    have hp0 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hp1.ne'
    simp only [dsFromS, cutRep, smul_add, smul_smul, inner_add_left, inner_rsmul_left,
      inner_rsmul_right]
    push_cast
    field_simp
  have hR : ∫ p, inner ℂ (cutRep c χ w p) (pdS φ p) ∂(cellMeasure c) =
      Lam c w (fun p => χ p • pdS φ p) := by
    unfold Lam
    congr 1
    funext p
    simp [cutRep]
  rw [hL, hR]
  linear_combination hweak

theorem ibp_eta {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {w Ew : HSpace c MeridC} (hE : N05_1_1Org.WeakEta c w Ew) {φ : Profile → MeridC}
    (hφ : IsMeridTest c φ) :
    ∫ p, inner ℂ ((fun p => cutRep c χ Ew p + cutRep c (pdEta χ) w p) p)
        (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (cutRep c χ w p) (pdEta φ p) ∂(cellMeasure c) := by
  have hSP := SP.of_cutoff hχ
  have hψ : IsMeridTest c (fun p => χ p • φ p) := mt_smul hSP hφ
  have h2 : IsMeridTest c (fun p => pdEta χ p • φ p) := mt_smul hSP.pdEta hφ
  have h3 : IsMeridTest c (fun p => χ p • pdEta φ p) := mt_smul hSP (mt_pdEta hφ)
  have hweak := weakE_lam hE hψ
  have hprod : pdEta (fun p => χ p • φ p) = fun p => χ p • pdEta φ p + pdEta χ p • φ p :=
    funext (pdEta_smul hχ.smooth hφ.smooth)
  rw [hprod, Lam_add hc w (nice_of_mt hc h3) (nice_of_mt hc h2)] at hweak
  have hL : ∫ p, inner ℂ ((fun p => cutRep c χ Ew p + cutRep c (pdEta χ) w p) p)
        (φ p) ∂(cellMeasure c) =
      Lam c Ew (fun p => χ p • φ p) + Lam c w (fun p => pdEta χ p • φ p) := by
    unfold Lam
    rw [← integral_add (integrable_inner_periodize hc Ew (nice_of_mt hc hψ))
      (integrable_inner_periodize hc w (nice_of_mt hc h2))]
    congr 1
    funext p
    simp only [cutRep, inner_add_left, inner_rsmul_left, inner_rsmul_right]
  have hR : ∫ p, inner ℂ (cutRep c χ w p) (pdEta φ p) ∂(cellMeasure c) =
      Lam c w (fun p => χ p • pdEta φ p) := by
    unfold Lam
    congr 1
    funext p
    simp [cutRep]
  rw [hL, hR]
  linear_combination hweak

/-- The function `χ φ`. -/
def psi0 (χ : Profile → ℝ) (φ : Profile → MeridC) : Profile → MeridC := fun p => χ p • φ p

theorem ibp_q {c σ H1 L1 ε : ℝ} (hc : 0 < c) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {w Sw Qw Ew : HSpace c MeridC} (hS : N05_1_1Org.WeakS c w Sw)
    (hQ : N05_1_1Org.WeakQ c ε w Qw) (hE : N05_1_1Org.WeakEta c w Ew)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    ∫ p, inner ℂ (dqFromSQE ε (cutRep c χ w)
        (fun p => cutRep c χ Sw p + cutRep c (fun p => p.1 * pdS χ p) w p)
        (fun p => cutRep c χ Qw p + cutRep c
          (fun p => pdQ χ p - ε * (2 * p.1 * pdS χ p + p.2.2 * pdEta χ p)) w p)
        (fun p => cutRep c χ Ew p + cutRep c (pdEta χ) w p) p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (cutRep c χ w p) (pdQ φ p) ∂(cellMeasure c) := by
  have hSP := SP.of_cutoff hχ
  have hψ0 : IsMeridTest c (psi0 χ φ) := mt_smul hSP hφ
  have hs : IsMeridTest c (fun p => p.1 • psi0 χ φ p) := mt_smul (SP.fst c) hψ0
  have he : IsMeridTest c (fun p => p.2.2 • psi0 χ φ p) := mt_smul (SP.eta c) hψ0
  -- weak identities
  have hQ' := weakQ_lam hQ hψ0
  have hS' := weakS_lam hS hs
  have hE' := weakE_lam hE he
  have hS'' : Lam c Sw (psi0 χ φ) = -Lam c w (pdS (fun p => p.1 • psi0 χ φ p)) := by
    rw [← hS']
    refine (Lam_congr Sw (fun p hp => ?_))
    have hp1 : 0 < p.1 := hp.1
    simp [smul_smul, hp1.ne']
  -- fields
  have hFQ : IsMeridTest c (fun p => pdQ (psi0 χ φ) p - ε •
      (opK (psi0 χ φ) p + (2 : ℝ) • psi0 χ φ p)) :=
    mt_sub (mt_pdQ hψ0) (mt_smul (SP.const c ε) (mt_add (mt_opK hψ0)
      (mt_smul (SP.const c 2) hψ0)))
  have hFS : IsMeridTest c (pdS (fun p => p.1 • psi0 χ φ p)) := mt_pdS hs
  have hFE : IsMeridTest c (pdEta (fun p => p.2.2 • psi0 χ φ p)) := mt_pdEta he
  have h3 : IsMeridTest c (fun p => χ p • pdQ φ p) := mt_smul hSP (mt_pdQ hφ)
  have h2 : IsMeridTest c (fun p => pdQ χ p • φ p) := mt_smul hSP.pdQ hφ
  have key : Lam c w (fun p => (pdQ (psi0 χ φ) p - ε •
        (opK (psi0 χ φ) p + (2 : ℝ) • psi0 χ φ p)) +
        (2 * ε) • pdS (fun p => p.1 • psi0 χ φ p) p +
        ε • pdEta (fun p => p.2.2 • psi0 χ φ p) p) =
      Lam c w (fun p => (χ p • pdQ φ p + pdQ χ p • φ p) + ε • psi0 χ φ p) := by
    refine Lam_congr w (fun p _ => ?_)
    have e1 : pdQ (psi0 χ φ) p = χ p • pdQ φ p + pdQ χ p • φ p :=
      pdQ_smul hχ.smooth hφ.smooth p
    have e2 : pdS (psi0 χ φ) p = χ p • pdS φ p + pdS χ p • φ p :=
      pdS_smul hχ.smooth hφ.smooth p
    have e3 : pdEta (psi0 χ φ) p = χ p • pdEta φ p + pdEta χ p • φ p :=
      pdEta_smul hχ.smooth hφ.smooth p
    have e4 : pdS (fun p => p.1 • psi0 χ φ p) p = p.1 • pdS (psi0 χ φ) p + (1 : ℝ) • psi0 χ φ p := by
      rw [pdS_smul contDiff_fst hψ0.smooth p, pdS_fst]
    have e5 : pdEta (fun p => p.2.2 • psi0 χ φ p) p =
        p.2.2 • pdEta (psi0 χ φ) p + (1 : ℝ) • psi0 χ φ p := by
      rw [pdEta_smul (g := fun p : Profile => p.2.2)
        (contDiff_snd.comp contDiff_snd : ContDiff ℝ ∞ (fun p : Profile => p.2.2))
        hψ0.smooth p, pdEta_eta]
    simp only [opK, opS]
    simp only [e1, e2, e3, e4, e5]
    simp only [psi0]
    module
  have hn1 := nice_of_mt hc hFQ
  have hn2 := nice_of_mt hc (mt_smul (SP.const c (2 * ε)) hFS)
  have hn3 := nice_of_mt hc (mt_smul (SP.const c ε) hFE)
  rw [Lam_add hc w (nice_of_mt hc (mt_add hFQ (mt_smul (SP.const c (2 * ε)) hFS))) hn3,
    Lam_add hc w hn1 hn2, Lam_smul, Lam_smul,
    Lam_add hc w (nice_of_mt hc (mt_add h3 h2)) (nice_of_mt hc (mt_smul (SP.const c ε) hψ0)),
    Lam_add hc w (nice_of_mt hc h3) (nice_of_mt hc h2), Lam_smul] at key
  -- the left integral
  have hn4 := nice_of_mt hc hψ0
  have hn5 := nice_of_mt hc (mt_smul (SP.const c (2 * ε)) hψ0)
  have hn6 := nice_of_mt hc (mt_smul (SP.const c ε) he)
  have hn7 := nice_of_mt hc (mt_add (mt_smul (SP.const c ε) hψ0) h2)
  have hL : ∫ p, inner ℂ (dqFromSQE ε (cutRep c χ w)
        (fun p => cutRep c χ Sw p + cutRep c (fun p => p.1 * pdS χ p) w p)
        (fun p => cutRep c χ Qw p + cutRep c
          (fun p => pdQ χ p - ε * (2 * p.1 * pdS χ p + p.2.2 * pdEta χ p)) w p)
        (fun p => cutRep c χ Ew p + cutRep c (pdEta χ) w p) p) (φ p) ∂(cellMeasure c) =
      Lam c Qw (psi0 χ φ) + Lam c Sw (fun p => (2 * ε) • psi0 χ φ p) +
        Lam c Ew (fun p => ε • (p.2.2 • psi0 χ φ p)) +
        Lam c w (fun p => ε • psi0 χ φ p + pdQ χ p • φ p) := by
    unfold Lam
    have i1 := integrable_inner_periodize hc Qw hn4
    have i2 := integrable_inner_periodize hc Sw hn5
    have i3 := integrable_inner_periodize hc Ew hn6
    have i4 := integrable_inner_periodize hc w hn7
    have I12 : Integrable (fun p => inner ℂ (periodize c (Qw : Profile → MeridC) p) (psi0 χ φ p) +
        inner ℂ (periodize c (Sw : Profile → MeridC) p) ((2 * ε) • psi0 χ φ p)) (cellMeasure c) :=
      i1.add i2
    have I123 : Integrable (fun p => inner ℂ (periodize c (Qw : Profile → MeridC) p) (psi0 χ φ p) +
        inner ℂ (periodize c (Sw : Profile → MeridC) p) ((2 * ε) • psi0 χ φ p) +
        inner ℂ (periodize c (Ew : Profile → MeridC) p) (ε • (p.2.2 • psi0 χ φ p)))
        (cellMeasure c) := I12.add i3
    rw [← integral_add i1 i2, ← integral_add I12 i3, ← integral_add I123 i4]
    congr 1
    funext p
    simp only [dqFromSQE, cutRep, psi0, smul_add, smul_smul, inner_add_left, inner_add_right,
      inner_rsmul_left, inner_rsmul_right]
    push_cast
    ring
  have hR : ∫ p, inner ℂ (cutRep c χ w p) (pdQ φ p) ∂(cellMeasure c) =
      Lam c w (fun p => χ p • pdQ φ p) := by
    unfold Lam
    congr 1
    funext p
    simp [cutRep]
  rw [hL, hR, Lam_smul Sw, Lam_smul Ew,
    Lam_add hc w (nice_of_mt hc (mt_smul (SP.const c ε) hψ0)) (nice_of_mt hc h2), Lam_smul w]
  push_cast at key ⊢
  linear_combination hQ' + (2 * (ε : ℂ)) * hS'' + (ε : ℂ) * hE' - key

end N05_1_1P

end UnforcedLeray.Short.PartIIa
