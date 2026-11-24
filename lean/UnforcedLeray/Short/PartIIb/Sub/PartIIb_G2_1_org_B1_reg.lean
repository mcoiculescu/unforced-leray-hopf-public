import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth

/-!
# Part II-b, `ORG:G2-1-B1-smooth`: joint-smoothness bridge for `PhysKOutLinComb` (R11)

Source of record: `the November 2 reference manuscript` (SP), lines 1214,
1665–1672, 2007–2010, and 2432–2437.

`PhysKOutLinComb` (`Sub/PartII-b_G2_1_org.lean:41`) omitted joint smoothness of `p.raw`, which is
needed so that `convT p.raw Φ` is continuous with compact spatial support (hence Bochner-integrable
against `NvC p.R b_i` on `phaseCell p.period` for `b_i ∈ InHr p.c bgp`). In `BgRegime p d dm dp`
for `p.ν ≤ ν_raw`, `PartIIIb.Concrete.rawJointSmooth` supplies
`ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2)`. Per R11, we add `PhysKOutLinCombSmooth` and
`physKopExists_of_smooth` beside `Sub/PartII-b_G2_1_org.lean` without modifying existing
declarations.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- (B1, smooth `p.raw` variant, SP 1214, 2007–2010): the physical output `IsKOut` is closed under
real linear combinations of `b` and `g` whenever `(τ, y) ↦ p.raw τ y` is jointly `C^∞` on
`ℝ × Space`. Composed by `PartII-b:G2/1` via `physKopExists_of_smooth`. -/
def PhysKOutLinCombSmooth : Prop :=
  ∀ (p : Params), 0 < p.ν → 0 < p.c → 0 < p.ε →
  ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) →
  ∀ (a : ℝ) (b₁ b₂ b : CProf) (g₁ g₂ : HpR p.c),
    InHr p.c bgp b₁ → InHr p.c bgp b₂ → InHr p.c bgp b →
    IsKOut p b₁ (toProf p.c g₁) → IsKOut p b₂ (toProf p.c g₂) →
    b =ᵐ[hMeas p.c bgp] (fun x => (a : ℂ) • b₁ x + b₂ x) →
    IsKOut p b (toProf p.c (a • g₁ + g₂))

open LinearBodySourceHelp in
/-- Conditional assembly of `PhysKopExists` (`PartII-b:G2/1`, SP 2007–2010, 2432–2437) from
`PhysRespLinComb`, `PhysKOutLinCombSmooth`, `PhysKOutUnique`, `PhysKOutExistsBound`, and
`PhysRespReal`, discharging joint smoothness of `p.raw` via
`PartIIIb.Concrete.rawJointSmooth`. -/
theorem physKopExists_of_smooth (hA : PhysRespLinComb) (hB : PhysKOutLinCombSmooth)
    (hU : PhysKOutUnique) (hC : PhysKOutExistsBound) (hD : PhysRespReal) : PhysKopExists := by
  intro dm dp hdm C_late k_late C_phys hCl hCp
  obtain ⟨ν_c, CK, k, hνc, hCK, hmain⟩ := hC dm dp hdm C_late k_late C_phys hCl hCp
  obtain ⟨ν_raw, hν_raw, Hraw⟩ := UnforcedLeray.Short.PartIIIb.Concrete.rawJointSmooth dm dp hdm
  refine ⟨min ν_c ν_raw, lt_min hνc hν_raw, fun p d hreg hν hε1 hper hlate hR => ?_⟩
  have hν1 : p.ν ≤ ν_c := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ ν_raw := hν.trans (min_le_right _ _)
  have hraw : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) :=
    Hraw p d hreg hν2
  have hc : 0 < p.c := by rw [hreg.c_eq]; exact inv_pos.2 (pow_pos p.ν_pos 2)
  have hε : 0 < p.ε := by rw [hreg.eps_eq]; exact Real.exp_pos _
  have hb : ∀ f : HpR p.c, ∃ b, InHr p.c bgp b ∧ (∀ x i, (b x i).im = 0) ∧
      IsResponse p.ν p.c p.ε 0 bgp (toProf p.c f) b := by
    intro f
    obtain ⟨b0, hb0, hb0R⟩ := (hR _ (RespOp.inHr_toProf hc f)).1
    exact hD p.ν p.c p.ε p.ν_pos hc hε f b0 hb0 hb0R
  choose b hbIn hbRe hbR using hb
  have hg : ∀ f : HpR p.c, ∃ g : HpR p.c, IsKOut p (b f) (toProf p.c g) ∧
      ‖g‖ ≤ CK * (p.ν ^ k)⁻¹ * ‖f‖ := by
    intro f
    obtain ⟨g, hg1, hg2⟩ := hmain p d hreg hν1 hε1 hper hlate (toProf p.c f) (b f)
      (RespOp.inHr_toProf hc f) (hbIn f) (hbRe f) ((hR _ (RespOp.inHr_toProf hc f)).2 _ (hbR f))
    refine ⟨g, hg1, ?_⟩
    rwa [hNorm_toProf hc, toReal_enorm] at hg2
  choose K hK1 hK2 using hg
  have hbae : ∀ (a : ℝ) (f₁ f₂ : HpR p.c),
      b (a • f₁ + f₂) =ᵐ[hMeas p.c bgp] (fun x => (a : ℂ) • b f₁ x + b f₂ x) := by
    intro a f₁ f₂
    set b' : CProf := fun x => (a : ℂ) • b f₁ x + b f₂ x with hb'
    have hb'In : InHr p.c bgp b' := PhysKopOrg.inHr_lincomb a (hbIn f₁) (hbIn f₂)
    have hF : toProf p.c (a • f₁ + f₂) =ᵐ[hMeas p.c bgp]
        fun x => (a : ℂ) • toProf p.c f₁ x + toProf p.c f₂ x := by
      filter_upwards [toProf_add_ae hc (a • f₁) f₂, toProf_smul_ae hc a f₁] with x h1 h2
      rw [h1, h2]
    have hb'R : IsResponse p.ν p.c p.ε 0 bgp (toProf p.c (a • f₁ + f₂)) b' :=
      hA p.ν p.c p.ε p.ν_pos hc hε a _ _ _ _ _ _ (RespOp.inHr_toProf hc f₁)
        (RespOp.inHr_toProf hc f₂) (hbIn f₁) (hbIn f₂) (RespOp.inHr_toProf hc _) hb'In
        (hbR f₁) (hbR f₂) hF Filter.EventuallyEq.rfl
    set d' : CProf := fun x => ((-1 : ℝ) : ℂ) • b (a • f₁ + f₂) x + b' x with hd'
    have hdIn : InHr p.c bgp d' := PhysKopOrg.inHr_lincomb (-1) (hbIn _) hb'In
    have hz : toProf p.c (0 : HpR p.c) =ᵐ[hMeas p.c bgp]
        fun x => ((-1 : ℝ) : ℂ) • toProf p.c (a • f₁ + f₂) x + toProf p.c (a • f₁ + f₂) x := by
      filter_upwards [toProf_zero_ae hc] with x hx
      rw [hx]
      simp
    have hdR : IsResponse p.ν p.c p.ε 0 bgp (toProf p.c (0 : HpR p.c)) d' :=
      hA p.ν p.c p.ε p.ν_pos hc hε (-1) _ _ _ _ _ _ (RespOp.inHr_toProf hc _)
        (RespOp.inHr_toProf hc _) (hbIn _) hb'In (RespOp.inHr_toProf hc _) hdIn
        (hbR _) hb'R hz Filter.EventuallyEq.rfl
    obtain ⟨Sb, Qb, Eb, -, -, -, hbd⟩ := (hR _ (RespOp.inHr_toProf hc 0)).2 _ hdR
    have h0 : hNorm p.c bgp (toProf p.c (0 : HpR p.c)) = 0 := by
      rw [hNorm_toProf hc]; simp
    have hle : hNorm p.c bgp d' ≤ 0 := by
      calc hNorm p.c bgp d' ≤ _ := le_self_add.trans (le_self_add.trans hbd)
        _ = 0 := by rw [h0]; simp
    have hz2 : hNorm p.c bgp d' = 0 := le_antisymm hle bot_le
    unfold hNorm at hz2
    rw [eLpNorm_eq_zero_iff hdIn.meas (by simp [bgp])] at hz2
    filter_upwards [hz2] with x hx
    have : ((-1 : ℝ) : ℂ) • b (a • f₁ + f₂) x + b' x = 0 := hx
    have h3 : b' x = b (a • f₁ + f₂) x := by
      have := congrArg (fun v => v + b (a • f₁ + f₂) x) this
      simpa using this
    exact h3.symm
  have hlin : ∀ (a : ℝ) (f₁ f₂ : HpR p.c), K (a • f₁ + f₂) = a • K f₁ + K f₂ := by
    intro a f₁ f₂
    refine hU p p.ν_pos hc hε (b (a • f₁ + f₂)) _ _ (hbIn _) (hK1 _) ?_
    exact hB p p.ν_pos hc hε hraw a (b f₁) (b f₂) _ (K f₁) (K f₂) (hbIn _) (hbIn _) (hbIn _)
      (hK1 f₁) (hK1 f₂) (hbae a f₁ f₂)
  have hK0 : K 0 = 0 := by
    have := hlin 1 0 0
    simp at this
    simpa using this
  let L : HpR p.c →ₗ[ℝ] HpR p.c :=
    { toFun := K
      map_add' := fun x y => by simpa using hlin 1 x y
      map_smul' := fun a x => by
        have := hlin a x 0
        simpa [hK0] using this }
  refine ⟨L.mkContinuous (CK * (p.ν ^ k)⁻¹) (fun f => ?_), fun f => ?_⟩
  · exact (hK2 f).trans (le_of_eq (by ring))
  · exact ⟨b f, hbIn f, hbR f, hK1 f⟩

end UnforcedLeray.Short.IIb

end
