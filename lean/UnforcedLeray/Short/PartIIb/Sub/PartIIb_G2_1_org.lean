import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2
import UnforcedLeray.Short.PartIIb.Tasks.ResponseOperator.Lift
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.LinearBodySource

/-!
# Part II-b, `PartII-b:G2/1/org`: `PhysKopExists` from four leaves

`K_ε = s B_{U_raw} T_ε` (SP 2007-2010; the response `T_ε` is SP 1665-1672, the late bound SP
2432-2437) is not definitional: `IsKOut` is a distributional identity, so `Kop` is built as
`f ↦ g_f`, where `b_f` is a response to `toProf f` and `g_f` is the output of `b_f`.  The leaves are
* `PhysRespLinComb`: `IsResponse` is closed under real linear combinations, up to a.e. (SP 1665-1672);
* `PhysKOutLinComb` / `PhysKOutUnique`: `IsKOut` is closed under linear combinations and `g` is
  determined by `b` (SP 2007-2010, linearity of `B_{U_raw}` and density of phase tests);
* `PhysKOutExistsBound`: existence of the output with the late bound (SP 2432-2437).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- (A) Responses `T_ε` are closed under real linear combinations, up to `hMeas`-a.e. equality of
sources and of responses (SP 1665-1672). -/
def PhysRespLinComb : Prop :=
  ∀ (ν c ε : ℝ), 0 < ν → 0 < c → 0 < ε →
  ∀ (a : ℝ) (F₁ F₂ b₁ b₂ F b : CProf),
    InHr c bgp F₁ → InHr c bgp F₂ → InHr c bgp b₁ → InHr c bgp b₂ → InHr c bgp F → InHr c bgp b →
    IsResponse ν c ε 0 bgp F₁ b₁ → IsResponse ν c ε 0 bgp F₂ b₂ →
    F =ᵐ[hMeas c bgp] (fun x => (a : ℂ) • F₁ x + F₂ x) →
    b =ᵐ[hMeas c bgp] (fun x => (a : ℂ) • b₁ x + b₂ x) →
    IsResponse ν c ε 0 bgp F b

/-- (B1) The physical output `IsKOut` is closed under real linear combinations of `b` and `g`
(SP 2007-2010). -/
def PhysKOutLinComb : Prop :=
  ∀ (p : Params), 0 < p.ν → 0 < p.c → 0 < p.ε →
  ∀ (a : ℝ) (b₁ b₂ b : CProf) (g₁ g₂ : HpR p.c),
    InHr p.c bgp b₁ → InHr p.c bgp b₂ → InHr p.c bgp b →
    IsKOut p b₁ (toProf p.c g₁) → IsKOut p b₂ (toProf p.c g₂) →
    b =ᵐ[hMeas p.c bgp] (fun x => (a : ℂ) • b₁ x + b₂ x) →
    IsKOut p b (toProf p.c (a • g₁ + g₂))

/-- (B2) The output class `g` is determined by `b` (phase tests separate `H_p` classes). -/
def PhysKOutUnique : Prop :=
  ∀ (p : Params), 0 < p.ν → 0 < p.c → 0 < p.ε →
  ∀ (b : CProf) (g g' : HpR p.c), InHr p.c bgp b →
    IsKOut p b (toProf p.c g) → IsKOut p b (toProf p.c g') → g = g'

/-- (D) The response to a real source `toProf f` has a real representative (the response equation has
real coefficients; SP 1665-1672).  Needed because `K_ε` is complex-linear, so the output exists as
an element of the real space `HpR` only for real `b`. -/
def PhysRespReal : Prop :=
  ∀ (ν c ε : ℝ), 0 < ν → 0 < c → 0 < ε → ∀ (f : HpR c) (b : CProf),
    InHr c bgp b → IsResponse ν c ε 0 bgp (toProf c f) b →
    ∃ b' : CProf, InHr c bgp b' ∧ (∀ x i, (b' x i).im = 0) ∧ IsResponse ν c ε 0 bgp (toProf c f) b'

/-- (C) Existence of the output with the late-coefficient bound (SP 2432-2437), for real `b`
(the statement for complex `b` is false: `K (i b) = i K b` is not real). -/
def PhysKOutExistsBound : Prop :=
  ∀ dm dp : ℝ, 0 < dm →
  ∀ (C_late : ℝ) (k_late : ℕ) (C_phys : ℝ), 0 < C_late → 0 < C_phys →
    ∃ (ν₀ CK : ℝ) (k : ℕ), 0 < ν₀ ∧ 0 < CK ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        p.ε ≤ 1 → 2 * p.ε * p.c ≤ 1 →
        (∀ S : ℝ, 1 ≤ S → ∀ (τ : ℝ) (y : Space), (y ∈ Axi.axis ∨ S < Axi.age p.R y) →
          DifferentiableAt ℝ (p.raw τ) y ∧
          ‖p.raw τ y‖ + ‖fderiv ℝ (p.raw τ) y‖ ≤
            C_late * (p.ν ^ k_late)⁻¹ * (S ^ (-(1 / 2 : ℝ)) + p.ε)) →
        ∀ F b : CProf, InHr p.c bgp F → InHr p.c bgp b → (∀ x i, (b x i).im = 0) →
          GraphBound p.ν p.c bgp p.ε C_phys F b →
          ∃ g : HpR p.c, IsKOut p b (toProf p.c g) ∧
            ‖g‖ ≤ CK * (p.ν ^ k)⁻¹ * (hNorm p.c bgp F).toReal

namespace PhysKopOrg

open LinearBodySourceHelp

theorem inHr_lincomb {c : ℝ} (a : ℝ) {b₁ b₂ : CProf} (h₁ : InHr c bgp b₁) (h₂ : InHr c bgp b₂) :
    InHr c bgp (fun x => (a : ℂ) • b₁ x + b₂ x) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [h₁.periodic, h₂.periodic] with x hx1 hx2
    simp only [hx1, hx2]
  · exact (h₁.meas.const_smul (a : ℂ)).add h₂.meas
  · unfold hNorm
    refine lt_of_le_of_lt (eLpNorm_add_le ((h₁.meas.const_smul (a : ℂ))) h₂.meas ?_) ?_
    · exact ENNReal.one_le_ofReal.2 (by norm_num [bgp])
    · refine ENNReal.add_lt_top.2 ⟨?_, h₂.finite⟩
      have := eLpNorm_const_smul (μ := hMeas c bgp) (p := ENNReal.ofReal bgp) (a : ℂ) b₁
      change eLpNorm ((a : ℂ) • b₁) _ _ < ⊤
      rw [this]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top h₁.finite

end PhysKopOrg

open LinearBodySourceHelp in
theorem physKopExists_of (hA : PhysRespLinComb) (hB : PhysKOutLinComb) (hU : PhysKOutUnique)
    (hC : PhysKOutExistsBound) (hD : PhysRespReal) : PhysKopExists := by
  intro dm dp hdm C_late k_late C_phys hCl hCp
  obtain ⟨ν₀, CK, k, hν₀, hCK, hmain⟩ := hC dm dp hdm C_late k_late C_phys hCl hCp
  refine ⟨ν₀, hν₀, fun p d hreg hν hε1 hper hlate hR => ?_⟩
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
    obtain ⟨g, hg1, hg2⟩ := hmain p d hreg hν hε1 hper hlate (toProf p.c f) (b f)
      (RespOp.inHr_toProf hc f) (hbIn f) (hbRe f) ((hR _ (RespOp.inHr_toProf hc f)).2 _ (hbR f))
    refine ⟨g, hg1, ?_⟩
    rwa [hNorm_toProf hc, toReal_enorm] at hg2
  choose K hK1 hK2 using hg
  -- a.e. uniqueness of the response
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
    exact hB p p.ν_pos hc hε a (b f₁) (b f₂) _ (K f₁) (K f₂) (hbIn _) (hbIn _) (hbIn _)
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
