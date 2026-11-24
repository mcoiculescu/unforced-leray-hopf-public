import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6.Inlet.Bridge
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6.Inlet.Integral
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletT0
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletLap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.EnvelopeParts
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.RawProfJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.InletJetDecay
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.JetLe
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.VecDiffJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.BEpsJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.ColVanish
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth

/-!
# Pointwise ring envelope of the linear inlet source (helper of `PartIII-b:C/rep/8/2/pres/3/2/6/1`)

Source `the November 2 reference manuscript`
2360-2386: off the axis the unprojected linear inlet source `D₀E_εα + E_εα·∇U_raw + U_raw·∇E_εα`
is the ring lift `N_v(𝒞_εα) = √s 𝒞_εα` of the complete source column
`𝒞_εα = s[(∂_s - νL_ε)e_ε + B_εe_ε]α` (Part II-b `InletL0Ptw`, `InletBPtw`, through the bridge
`realC_physSrc`), and the column has the envelope `A ν^{-k} s (1+|η|)^N e^{-κ|η|/c}`, vanishing for
`s > H/2` (Part II-b `ColEnvelope`, which needs the raw jet bound `RawJetBound`, SP 2419-2423).
Hence the source is bounded by the ring envelope `ringEnv` with `M = 2Aν^{-k}|α|`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0412 UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet

open UnforcedLeray.Cons.C03.Concrete (Params)

theorem cplx_sum (f : Fin 2 → UnforcedLeray.Short.IIb.Coord → Merid) (a : Fin 2 → ℝ) :
    (fun m => ∑ i : Fin 2, ((a i : ℝ) : ℂ) • UnforcedLeray.Short.IIb.cplx (f i) m) =
      UnforcedLeray.Short.IIb.cplx (fun m => ∑ i : Fin 2, a i • f i m) := by
  funext m
  ext j
  simp [UnforcedLeray.Short.IIb.cplx, Fin.sum_univ_two]

/-- **The linear inlet source is bounded by a ring envelope** (source 2360-2386), given the raw
jet bound (SP 2419-2423). -/
theorem lin_ptw (hR : UnforcedLeray.Short.IIb.RawJetBound) :
    ∀ (Sig : ℝ) (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile), 0 < Sig →
      UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
    ∀ dm dp : ℝ, 0 < dm → ∃ (A κ : ℝ) (k N : ℕ) (ν₀ : ℝ), 0 < A ∧ 0 < κ ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ),
        UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∀ (α : Fin 2 → ℝ) (τ : ℝ) (y : Space), y ∉ axis →
          ‖inletLinSrc p α τ y‖ ≤
            ringEnv p.H (2 * A * (p.ν ^ k)⁻¹ * ‖α‖) κ p.c N (age p.R y) (trans p.R y) := by
  intro Sig lam q hSig hq dm dp hdm
  have hEnv : UnforcedLeray.Short.IIb.ColEnvelope :=
    UnforcedLeray.Short.IIb.colEnvelope_of_parts (UnforcedLeray.Short.IIb.rawProfJet_of hR)
      UnforcedLeray.Short.IIb.inletJetDecay UnforcedLeray.Short.IIb.jetLe
      UnforcedLeray.Short.IIb.vecDiffJet UnforcedLeray.Short.IIb.bEpsJet
      UnforcedLeray.Short.IIb.colVanish
  obtain ⟨A, κ, k, N, ν₀, hA, hκ, hν₀, hν₀1, HE⟩ := hEnv Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, hν₁, HL0⟩ := UnforcedLeray.Short.IIb.inletL0Ptw_of inletT0Ptw
    UnforcedLeray.Short.IIb.inletLapPtw Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, hν₂, HB⟩ := UnforcedLeray.Short.IIb.inletBPtw Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₃, hν₃, HS⟩ := UnforcedLeray.Short.IIb.inletJointSmooth Sig lam q hSig hq dm dp hdm
  refine ⟨A, κ, k, N, min ν₀ (min ν₁ (min ν₂ ν₃)),
    hA, hκ, lt_min hν₀ (lt_min hν₁ (lt_min hν₂ hν₃)), (min_le_left _ _).trans hν₀1, ?_⟩
  intro p d hreg hν hS hm α τ y hy
  have h0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have h1 : p.ν ≤ ν₁ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h2 : p.ν ≤ ν₂ := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have h3 : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  set α' : UnforcedLeray.Cons.C03.Concrete.E2 := WithLp.toLp 2 α with hα'
  have hα'i : ∀ i, α' i = α i := fun i => rfl
  -- the jointly smooth affine inlet and the raw field
  set G : ℝ × Space → Space := fun x => ∑ i : Fin 2, α i • p.inlet i x.1 x.2 with hGdef
  have hG : ContDiff ℝ ∞ G :=
    ContDiff.sum fun i _ => (HS p d hreg h3 hS hm i).const_smul (α i)
  have hG2 : ContDiff ℝ 2 G := hG.of_le (by norm_num)
  have hRaw : ContDiffOn ℝ 2 (fun x : ℝ × Space => p.raw x.1 x.2) offAxis :=
    rawU_contDiffOn_offAxis_of p p.ε_pos (hreg.train_stream_smooth.of_le (by norm_num))
  have hU : DifferentiableAt ℝ (fun x : ℝ × Space => p.raw x.1 x.2) (τ, y) :=
    (hRaw.differentiableOn (by norm_num)).differentiableAt
      (isOpen_offAxis.mem_nhds (show (τ, y) ∈ offAxis from hy))
  have hbr := realC_physSrc p.ν hG2 τ y hU
  have hIC : UnforcedLeray.Short.IIb.inletC p α' = fun x => realC (G x) := by
    funext x
    simp only [UnforcedLeray.Short.IIb.inletC, Params.Efun, hGdef, rc_sum, rc_csmul, hα'i]
  have hUf : p.Ufun = fun x => realC (p.raw x.1 x.2) := rfl
  have hL := HL0 p d hreg h1 hS hm α' τ y hy
  have hBp := HB p d hreg h2 hS hm α' τ y hy
  rw [hIC] at hL
  rw [hIC, hUf] at hBp
  rw [add_assoc, hL, hBp, cplx_sum, cplx_sum, UnforcedLeray.Short.IIb.NvC_cplx,
    UnforcedLeray.Short.IIb.NvC_cplx] at hbr
  simp only [hα'i] at hbr
  set fD : UnforcedLeray.Short.IIb.Coord → Merid := fun m =>
    ∑ i : Fin 2, α i • UnforcedLeray.Short.IIb.colDiffR p i m with hfD
  set fI : UnforcedLeray.Short.IIb.Coord → Merid := fun m =>
    ∑ i : Fin 2, α i • UnforcedLeray.Short.IIb.colIntR p i m with hfI
  have hsrc : inletLinSrc p α τ y = Nv p.R (fD + fI) τ y := by
    have e : realC (inletLinSrc p α τ y) = realC (Nv p.R (fD + fI) τ y) := by
      rw [Nv_add, rc_add]
      exact hbr
    have hinj : Function.Injective (realC : Space → PhaseSpace.CVec3) := by
      intro a b hab
      have : ‖a - b‖ = 0 := by rw [← rc_norm, rc_sub, hab, sub_self, norm_zero]
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    exact hinj e
  -- the chart point
  have hRne : p.R ≠ 0 := p.R_pos.ne'
  set x : ℝ × (ℝ × ℝ) := chart p.R τ y with hx
  have hs0 : 0 < x.1 := age_pos hRne hy
  have hx1 : x.1 = age p.R y := rfl
  have hx2 : x.2.2 = trans p.R y := rfl
  have hcol : (fD + fI) x = ∑ i : Fin 2, α i • UnforcedLeray.Short.IIb.colEpsR p i x := by
    simp only [Pi.add_apply, hfD, hfI, UnforcedLeray.Short.IIb.colEpsR, hs0, if_true, smul_add,
      Finset.sum_add_distrib]
  rw [hsrc, norm_Nv p.R _ τ hy, ← hx, hcol, ← hx1, ← hx2]
  have HE' := HE p d ⟨hreg, h0, hS, hm⟩
  have hvan : ∀ i, _ := fun i => (HE' i).1
  have hbd : ∀ i, _ := fun i => (HE' i).2
  have hM : 0 ≤ 2 * A * (p.ν ^ k)⁻¹ * ‖α‖ := by
    have := p.ν_pos
    positivity
  by_cases hle : x.1 ≤ p.H / 2
  · rw [ringEnv_of_mem hs0 hle]
    have hsum : ‖∑ i : Fin 2, α i • UnforcedLeray.Short.IIb.colEpsR p i x‖ ≤
        2 * ‖α‖ * (A * (p.ν ^ k)⁻¹ * x.1 * (1 + |x.2.2|) ^ N *
          Real.exp (-(κ * |x.2.2| / p.c))) := by
      refine (norm_sum_le _ _).trans ?_
      rw [Fin.sum_univ_two, norm_smul, norm_smul]
      have hb0 := hbd 0 x hs0 hle
      have hb1 := hbd 1 x hs0 hle
      have ha0 : ‖α 0‖ ≤ ‖α‖ := norm_le_pi_norm α 0
      have ha1 : ‖α 1‖ ≤ ‖α‖ := norm_le_pi_norm α 1
      have hE : 0 ≤ A * (p.ν ^ k)⁻¹ * x.1 * (1 + |x.2.2|) ^ N *
          Real.exp (-(κ * |x.2.2| / p.c)) := by
        have := p.ν_pos
        positivity
      calc ‖α 0‖ * ‖UnforcedLeray.Short.IIb.colEpsR p 0 x‖ +
            ‖α 1‖ * ‖UnforcedLeray.Short.IIb.colEpsR p 1 x‖
          ≤ ‖α‖ * (A * (p.ν ^ k)⁻¹ * x.1 * (1 + |x.2.2|) ^ N *
              Real.exp (-(κ * |x.2.2| / p.c))) +
            ‖α‖ * (A * (p.ν ^ k)⁻¹ * x.1 * (1 + |x.2.2|) ^ N *
              Real.exp (-(κ * |x.2.2| / p.c))) := by
            gcongr
        _ = _ := by ring
    calc √x.1 * ‖∑ i : Fin 2, α i • UnforcedLeray.Short.IIb.colEpsR p i x‖
        ≤ √x.1 * (2 * ‖α‖ * (A * (p.ν ^ k)⁻¹ * x.1 * (1 + |x.2.2|) ^ N *
          Real.exp (-(κ * |x.2.2| / p.c)))) :=
          mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
      _ = 2 * A * (p.ν ^ k)⁻¹ * ‖α‖ * (√x.1 * x.1) *
          ((1 + |x.2.2|) ^ N * Real.exp (-(κ * |x.2.2| / p.c))) := by ring
      _ = _ := by rw [sqrt_mul_self_eq_rpow hs0.le]
  · have hz : ∀ i, UnforcedLeray.Short.IIb.colEpsR p i x = 0 :=
      fun i => hvan i x (not_le.1 hle)
    simp only [hz, smul_zero, Finset.sum_const_zero, norm_zero, mul_zero]
    exact ringEnv_nonneg hM _ _

end UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet
