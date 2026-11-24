import UnforcedLeray.Short.PartIIb.Tasks.ResponseOperator
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.FreeResponseCongr
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.AbsPhaseIBP
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletGood
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawGood
import UnforcedLeray.Short.PartIIb.StatementsNonlinear

/-!
# Part II-b, task `PartII-b:P3`: `row_ordRel`

Source of record: `the November 2 reference manuscript`, lines 2490-2498.

If `rowOp Ke Ce y = J f` (`f ∈ p.Y`) and `Θ` is a response operator as in `PartII-b:P2`
(mapping `y = (f', α)` to `(w, νΔw, T₀w, R^{2/p} α)` with `rep w =ᵃᵉ NvC p.R b` for the
response profile `b` of `toProf p.c f'`), then `p.OrdRel (Θ y) (f : Yq p.period q0E)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.RieszLp UnforcedLeray.Short.PartIIa
  UnforcedLeray.Short.IIb.RespOp UnforcedLeray.Short.IIb.FreeRespCongrHelp
  UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0190 UnforcedLeray.Blueprint

/-! ## 1. `HasPhaseOp (L0T p.ν) (p.wOf z) (p.A0 z)` on the graph space -/

theorem hasPhaseOp_A0 (p : Params) (z : p.Z) :
    HasPhaseOp (L0T p.ν) (p.wOf z) (p.A0 z) := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  obtain ⟨hw, ha, hb⟩ := mem_XGraph_iff.1 ((mem_graphSpace p.period).1 z.2).1
  have hLap : HasPhaseOp (nuLapT p.ν) (p.wOf z) (cΔ p.period (z : Amb p.period)) := by
    rw [← ha]
    exact hasPhaseOp_nuLapX ⟨cw p.period (z : Amb p.period), hw⟩
  have hT0 : HasPhaseOp driftT (p.wOf z) (cT p.period (z : Amb p.period)) := by
    rw [← hb]
    exact hasPhaseOp_T0X ⟨cw p.period (z : Amb p.period), hw⟩
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  have hsm : ((1 / 2 : ℂ) • p.wOf z : Yq p.period q0E) = (1 / 2 : ℝ) • p.wOf z := by
    rw [h12]
    rfl
  have hEq : cT p.period (z : Amb p.period) - cΔ p.period (z : Amb p.period) -
      (1 / 2 : ℂ) • p.wOf z = p.A0 z := by
    rw [hsm]
    rfl
  rw [← hEq]
  exact hasPhaseOp_L0T hLap hT0

/-! ## 2. Linearity of `g ↦ pairF p.period Φ (NvC p.R (toProf p.c g))` via `RespOp.liftY` -/

theorem pairF_nvC_toProf_eq_phasePair (p : Params) (g : HpR p.c)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period Φ (NvC p.R (toProf p.c g)) =
      phasePair p.period q0E Φ (liftY p g) := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  rw [phasePair_eq_pairF_rep hΦ]
  exact (pairF_congr_ae' p.period Φ _ _ (rep_ae_eq_of_hasRepY (hasRepY_liftY p g))).symm

theorem pairF_nvC_toProf_add (p : Params) (g₁ g₂ : HpR p.c)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period Φ (NvC p.R (toProf p.c (g₁ + g₂))) =
      pairF p.period Φ (NvC p.R (toProf p.c g₁)) +
        pairF p.period Φ (NvC p.R (toProf p.c g₂)) := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  rw [pairF_nvC_toProf_eq_phasePair p (g₁ + g₂) hΦ,
    pairF_nvC_toProf_eq_phasePair p g₁ hΦ,
    pairF_nvC_toProf_eq_phasePair p g₂ hΦ,
    liftY_add, map_add]

theorem pairF_nvC_toProf_smul (p : Params) (a : ℝ) (g : HpR p.c)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period Φ (NvC p.R (toProf p.c (a • g))) =
      (a : ℂ) * pairF p.period Φ (NvC p.R (toProf p.c g)) := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hsm : a • liftY p g = (a : ℂ) • liftY p g := rfl
  rw [pairF_nvC_toProf_eq_phasePair p (a • g) hΦ,
    pairF_nvC_toProf_eq_phasePair p g hΦ,
    liftY_smul, hsm, map_smul, smul_eq_mul]

/-! ## 3. Unfolding `rowOp` and decomposing `E2` along the standard basis -/

theorem rowOp_apply_eq {c : ℝ} (Ke : HpR c →L[ℝ] HpR c) (Ce : E2 →L[ℝ] HpR c)
    (y : RowSpace c) :
    rowOp Ke Ce y = y.ofLp.1 + Ke y.ofLp.1 + Ce y.ofLp.2 := by
  change (ContinuousLinearMap.id ℝ (HpR c) + Ke) y.ofLp.1 + Ce y.ofLp.2 = _
  rfl

theorem E2_eq_sum_single (α : E2) :
    α = α 0 • EuclideanSpace.single 0 (1 : ℝ) + α 1 • EuclideanSpace.single 1 (1 : ℝ) := by
  ext j
  fin_cases j <;>
    simp [PiLp.add_apply, PiLp.smul_apply]

/-! ## 4. Algebraic deduction of `OrdRel` from `rowOp Ke Ce y = J f` -/

/-- If `Θ : RowSpace p.c →L[ℝ] p.Z` has the coordinate and representation properties of `PartII-b:P2`
and `J : p.Y →L[ℝ] HpR p.c` has the representation property of `PartII-b:P1`, and if `pairF` splits
additively over `L0T p.ν Φ + convT p.raw Φ` against `p.Efun i` for solenoidal tests `Φ`, then
`rowOp Ke Ce y = J f` implies `p.OrdRel (Θ y) (f : Yq p.period q0E)`. -/
theorem row_ordRel_of_split (p : Params)
    {Ke : HpR p.c →L[ℝ] HpR p.c} {Ce : E2 →L[ℝ] HpR p.c}
    (hK : IsKop p Ke) (hC : IsCop p Ce)
    {Θ : RowSpace p.c →L[ℝ] p.Z}
    (hcoord : ∀ y : RowSpace p.c, p.coord (Θ y) = y.ofLp.2.ofLp)
    (hrep : ∀ (y : RowSpace p.c) (b : CProf),
      IsResponse p.ν p.c p.ε 0 bgp (toProf p.c y.ofLp.1) b →
        (∀ᵐ x : ℝ × Space, rep (p.wOf (Θ y)) x.1 x.2 = NvC p.R b x) ∧
          HasRep (p.wOf (Θ y)) (NvC p.R b))
    {J : p.Y →L[ℝ] HpR p.c}
    (hJ : ∀ f : p.Y, ∀ᵐ x : ℝ × Space,
      rep (f : Yq p.period q0E) x.1 x.2 = NvC p.R (toProf p.c (J f)) x)
    (hsplit : ∀ (i : Fin 2) (Φ : ℝ × Space → CVec3), IsSolTest p.period Φ →
      pairF p.period (fun x => L0T p.ν Φ x + convT p.raw Φ x) (p.Efun i) =
        pairF p.period (L0T p.ν Φ) (p.Efun i) + pairF p.period (convT p.raw Φ) (p.Efun i))
    (y : RowSpace p.c) (f : p.Y) (hrow : rowOp Ke Ce y = J f) :
    p.OrdRel (Θ y) (f : Yq p.period q0E) := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  intro Φ hΦ
  obtain ⟨b, -, hb_resp, hb_kout⟩ := hK y.ofLp.1
  obtain ⟨hrep_ae, -⟩ := hrep y b hb_resp
  -- 1. Identify `⟨Φ, A₀(Θ y)⟩ = pairF Φ (NvC R (toProf c y.1))`
  have hA0 : phasePair p.period q0E Φ (p.A0 (Θ y)) =
      pairF p.period Φ (NvC p.R (toProf p.c y.ofLp.1)) := by
    have h1 : phasePair p.period q0E Φ (p.A0 (Θ y)) =
        phasePair p.period q0E (L0T p.ν Φ) (p.wOf (Θ y)) :=
      (hasPhaseOp_A0 p (Θ y) Φ hΦ.1).symm
    have h2 : phasePair p.period q0E (L0T p.ν Φ) (p.wOf (Θ y)) =
        pairF p.period (L0T p.ν Φ) (NvC p.R b) := by
      rw [phasePair_eq_pairF_rep (isPhaseTest_L0T hΦ.1 p.ν)]
      exact pairF_congr_ae' p.period (L0T p.ν Φ) _ _ hrep_ae
    have h3 : pairF p.period (L0T p.ν Φ) (NvC p.R b) =
        pairF p.period Φ (NvC p.R (toProf p.c y.ofLp.1)) := by
      have heq := hb_resp.equation Φ hΦ
      have h0 : (fun x : ℝ × Space => L0T p.ν Φ x + (0 : ℂ) • Φ x) = L0T p.ν Φ := by
        funext x
        simp
      rwa [h0] at heq
    rw [h1, h2, h3]
  -- 2. Identify `pairF (convT raw Φ) (rep (wOf (Θ y))) = pairF Φ (NvC R (toProf c (Ke y.1)))`
  have hKterm : pairF p.period (convT p.raw Φ) (fun x => rep (p.wOf (Θ y)) x.1 x.2) =
      pairF p.period Φ (NvC p.R (toProf p.c (Ke y.ofLp.1))) := by
    rw [pairF_congr_ae' p.period (convT p.raw Φ) _ _ hrep_ae, hb_kout Φ hΦ.1]
  -- 3. Identify the inlet column sum via `IsCop` and `hsplit`
  have hCi : ∀ i : Fin 2,
      pairF p.period Φ (NvC p.R (toProf p.c (Ce (EuclideanSpace.single i (1 : ℝ))))) =
        pairF p.period (L0T p.ν Φ) (p.Efun i) + pairF p.period (convT p.raw Φ) (p.Efun i) := by
    intro i
    have h1 := (hC (EuclideanSpace.single i (1 : ℝ)) Φ hΦ.1).symm
    have h2 : (fun x : ℝ × Space =>
        ∑ j : Fin 2, (((EuclideanSpace.single i (1 : ℝ) : E2) j : ℝ) : ℂ) • p.Efun j x) =
        p.Efun i :=
      funext fun x => sum_single_smul i (fun j => p.Efun j x)
    rw [h1, h2, hsplit i Φ hΦ]
  have hCe_decomp : Ce y.ofLp.2 =
      y.ofLp.2 0 • Ce (EuclideanSpace.single 0 (1 : ℝ)) +
        y.ofLp.2 1 • Ce (EuclideanSpace.single 1 (1 : ℝ)) := by
    conv_lhs => rw [E2_eq_sum_single y.ofLp.2]
    rw [map_add, map_smul, map_smul]
  have hCterm : pairF p.period Φ (NvC p.R (toProf p.c (Ce y.ofLp.2))) =
      ∑ i : Fin 2, (p.coord (Θ y) i : ℂ) *
        (pairF p.period (L0T p.ν Φ) (p.Efun i) +
          pairF p.period (convT p.raw Φ) (p.Efun i)) := by
    rw [hCe_decomp,
      pairF_nvC_toProf_add p _ _ hΦ.1,
      pairF_nvC_toProf_smul p _ _ hΦ.1,
      pairF_nvC_toProf_smul p _ _ hΦ.1,
      hCi 0, hCi 1, Fin.sum_univ_two, hcoord y]
  -- 4. Identify `⟨Φ, f⟩ = pairF Φ (NvC R (toProf c (J f)))` and expand `J f = rowOp Ke Ce y`
  have hf_lhs : phasePair p.period q0E Φ (f : Yq p.period q0E) =
      pairF p.period Φ (NvC p.R (toProf p.c (J f))) := by
    rw [phasePair_eq_pairF_rep hΦ.1]
    exact pairF_congr_ae' p.period Φ _ _ (hJ f)
  have hrow' : J f = y.ofLp.1 + Ke y.ofLp.1 + Ce y.ofLp.2 := by
    rw [← hrow, rowOp_apply_eq]
  rw [hf_lhs, hrow',
    pairF_nvC_toProf_add p (y.ofLp.1 + Ke y.ofLp.1) (Ce y.ofLp.2) hΦ.1,
    pairF_nvC_toProf_add p y.ofLp.1 (Ke y.ofLp.1) hΦ.1,
    hA0, hKterm, hCterm]

/-! ## 5. Splitting `pairF` on `L0T ν Φ + convT V Φ` for fields vanishing near the axis -/

theorem continuous_gradUT {V : ℝ → SpatialField} {Φ : ℝ × Space → CVec3}
    (hV : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2)) (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (gradUT V Φ) := by
  have hVc : ContDiff ℝ ∞ (fun w : ℝ × Space => realC (V w.1 w.2)) := contDiff_realC_field hV
  have heq : gradUT V Φ = fun x => WithLp.toLp 2 (fun k : Fin 3 =>
      ∑ i : Fin 3, Φ x i * dy k (fun w : ℝ × Space => realC (V w.1 w.2)) x i) := by
    funext x
    ext k
    simp [gradUT, dy_realC_comp hV k _ x]
  rw [heq]
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
  refine continuous_finsetSum _ fun i _ => ?_
  exact (srwf_coord_contDiff hΦ i).continuous.mul
    (srwf_coord_contDiff (UnforcedLeray.PhaseSpace.contDiff_dy hVc k) i).continuous

theorem continuous_convT {V : ℝ → SpatialField} {Φ : ℝ × Space → CVec3}
    (hV : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2)) (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (convT V Φ) := by
  have hVc : ContDiff ℝ ∞ (fun w : ℝ × Space => realC (V w.1 w.2)) := contDiff_realC_field hV
  have hadv : Continuous (advT (fun x => realC (V x.1 x.2)) Φ) := by
    unfold advT
    exact continuous_finsetSum _ fun k _ =>
      (srwf_coord_contDiff hVc k).continuous.smul
        (UnforcedLeray.PhaseSpace.contDiff_dy hΦ k).continuous
  exact (continuous_gradUT hV hΦ).sub hadv

theorem convT_eq_zero_of_norm_gt {V : ℝ → SpatialField} {Φ : ℝ × Space → CVec3} {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → Φ (τ, y) = 0) (τ : ℝ) (y : Space) (hy : R < ‖y‖) :
    convT V Φ (τ, y) = 0 := by
  have hgrad : gradUT V Φ (τ, y) = 0 := by
    ext k
    simp [gradUT, hR τ y hy]
  have hadv : advT (fun x : ℝ × Space => realC (V x.1 x.2)) Φ (τ, y) = 0 := by
    unfold advT
    exact Finset.sum_eq_zero fun k _ => by rw [srwf_dy_bdd hR k τ y hy, smul_zero]
  simp [convT, hgrad, hadv]

/-- If `V` is `C^∞` off the symmetry axis and `E` is continuous and vanishes on a thin tube
`ϱ < δ` (`δ > 0`), then `pairF P (L0T ν Φ + convT V Φ) E = pairF P (L0T ν Φ) E + pairF P (convT V Φ) E`
for every phase test `Φ`. -/
theorem pairF_add_convT_of_vanish_near_axis {P ν : ℝ} {V : ℝ → SpatialField}
    {E : ℝ × Space → CVec3}
    (hVon : ContDiffOn ℝ ∞ (fun x : ℝ × Space => V x.1 x.2) {x | x.2 ∉ Axi.axis})
    (hE : Continuous E)
    {δ : ℝ} (hδpos : 0 < δ) (hEδ : ∀ τ y, Axi.ϱ y < δ → E (τ, y) = 0)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    pairF P (fun x => L0T ν Φ x + convT V Φ x) E =
      pairF P (L0T ν Φ) E + pairF P (convT V Φ) E := by
  set χ : Space → ℝ := fun y => Real.smoothTransition ((Axi.ϱ y - δ / 4) / (δ / 4))
  have hq : 0 < δ / 4 := by positivity
  have hχ1 : ∀ y, δ / 2 ≤ Axi.ϱ y → χ y = 1 := by
    intro y hy
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hq]
    linarith
  have hχ0 : ∀ y, Axi.ϱ y ≤ δ / 4 → χ y = 0 := by
    intro y hy
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hq.le
  obtain ⟨V', hV'def⟩ : ∃ V' : ℝ → SpatialField, ∀ τ y, V' τ y = χ y • V τ y :=
    ⟨fun τ y => χ y • V τ y, fun _ _ => rfl⟩
  have hOffOpen : IsOpen {x : ℝ × Space | x.2 ∉ Axi.axis} :=
    (Axi.isClosed_axis.isOpen_compl).preimage continuous_snd
  have hcontϱ : Continuous fun x : ℝ × Space => Axi.ϱ x.2 := Axi.continuous_ϱ.comp continuous_snd
  have hV'c : ContDiff ℝ ∞ (fun x : ℝ × Space => V' x.1 x.2) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases h : Axi.ϱ x.2 < δ / 4
    · have hev : (fun w : ℝ × Space => V' w.1 w.2) =ᶠ[𝓝 x] fun _ => (0 : Space) := by
        filter_upwards [(isOpen_lt hcontϱ continuous_const).mem_nhds h] with w hw
        rw [hV'def, hχ0 _ hw.le, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hle : δ / 4 ≤ Axi.ϱ x.2 := not_lt.1 h
      have hy : x.2 ∉ Axi.axis := fun h' => by
        have := (Axi.mem_axis_iff _).1 h'
        linarith
      have h1 : ContDiffAt ℝ ∞ (fun w : ℝ × Space => V w.1 w.2) x :=
        hVon.contDiffAt (hOffOpen.mem_nhds hy)
      have hϱc : ContDiffAt ℝ ∞ Axi.ϱ x.2 :=
        Axi.contDiffOn_ϱ.contDiffAt (Axi.isClosed_axis.isOpen_compl.mem_nhds hy)
      have hχc : ContDiffAt ℝ ∞ (fun w : ℝ × Space => χ w.2) x := by
        have h2 : ContDiffAt ℝ ∞ (fun w : ℝ × Space => (Axi.ϱ w.2 - δ / 4) / (δ / 4)) x :=
          ((hϱc.comp x contDiff_snd.contDiffAt).sub contDiffAt_const).div_const _
        exact (Real.smoothTransition.contDiff.contDiffAt).comp x h2
      have := hχc.smul h1
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      exact hV'def w.1 w.2
  have hlocS : ∀ τ y, δ ≤ Axi.ϱ y → ∀ᶠ y' in 𝓝 y, V' τ y' = V τ y' := by
    intro τ y hy
    filter_upwards [(isOpen_lt continuous_const Axi.continuous_ϱ).mem_nhds
      (show δ / 2 < Axi.ϱ y by linarith)] with w hw
    rw [hV'def, hχ1 _ hw.le, one_smul]
  have hpt : ∀ τ y, δ ≤ Axi.ϱ y → V' τ y = V τ y := by
    intro τ y hy
    rw [hV'def, hχ1 _ (by linarith), one_smul]
  have hEz : ∀ x : ℝ × Space, E x ≠ 0 → δ ≤ Axi.ϱ x.2 := by
    intro x hx
    by_contra h
    exact hx (hEδ x.1 x.2 (not_le.1 h))
  have hfd : ∀ x : ℝ × Space, δ ≤ Axi.ϱ x.2 → fderiv ℝ (V' x.1) x.2 = fderiv ℝ (V x.1) x.2 :=
    fun x hx => Filter.EventuallyEq.fderiv_eq (hlocS x.1 x.2 hx)
  have hconv_eq : ∀ x : ℝ × Space, E x ≠ 0 → convT V' Φ x = convT V Φ x := by
    intro x hx
    have hxδ := hEz x hx
    simp only [convT, gradUT, advT, hfd x hxδ, hpt x.1 x.2 hxδ]
  have hL : pairF P (fun x => L0T ν Φ x + convT V Φ x) E =
      phaseInt P (fun z => dotL (L0T ν Φ z) (E z) + dotL (convT V' Φ z) (E z)) := by
    unfold pairF
    congr 1
    funext x
    beta_reduce
    by_cases hx : E x = 0
    · simp [hx]
    · rw [← hconv_eq x hx, map_add]
      rfl
  have hR2 : pairF P (convT V Φ) E =
      phaseInt P (fun z => dotL (convT V' Φ z) (E z)) := by
    unfold pairF
    congr 1
    funext x
    by_cases hx : E x = 0
    · simp [hx]
    · rw [hconv_eq x hx]
  have hA_int : Integrable (fun z => dotL (L0T ν Φ z) (E z)) (srwfSlab P) := by
    have hL0Φ := isPhaseTest_L0T hΦ ν
    obtain ⟨RL, hRL⟩ := hL0Φ.bounded_support
    have hAc : Continuous (fun z => dotL (L0T ν Φ z) (E z)) :=
      (dotL.continuous.comp hL0Φ.continuous).clm_apply hE
    exact UnforcedLeray.B0005.integrable_slab (𝒯 := P) hAc (R := RL)
      (fun t y hy => by simp [hRL t y hy])
  have hB_int : Integrable (fun z => dotL (convT V' Φ z) (E z)) (srwfSlab P) := by
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    have hBc : Continuous (fun z => dotL (convT V' Φ z) (E z)) :=
      (dotL.continuous.comp (continuous_convT hV'c hΦ.smooth)).clm_apply hE
    exact UnforcedLeray.B0005.integrable_slab (𝒯 := P) hBc (R := R)
      (fun t y hy => by simp [convT_eq_zero_of_norm_gt hR t y hy])
  have eAB : phaseInt P (fun z => dotL (L0T ν Φ z) (E z) + dotL (convT V' Φ z) (E z)) =
      P⁻¹ • ∫ z, (dotL (L0T ν Φ z) (E z) + dotL (convT V' Φ z) (E z)) ∂(srwfSlab P) :=
    srwf_phaseInt_eq (hA_int.add hB_int)
  have eA : pairF P (L0T ν Φ) E = P⁻¹ • ∫ z, dotL (L0T ν Φ z) (E z) ∂(srwfSlab P) :=
    srwf_phaseInt_eq hA_int
  have eB : phaseInt P (fun z => dotL (convT V' Φ z) (E z)) =
      P⁻¹ • ∫ z, dotL (convT V' Φ z) (E z) ∂(srwfSlab P) :=
    srwf_phaseInt_eq hB_int
  rw [hL, hR2, eAB, eA, eB, integral_add hA_int hB_int, smul_add]

/-! ## 6. Vanishing of `p.Efun i` near the symmetry axis and smoothness of `p.raw` off the axis -/

theorem inletProfile_eq_zero_of_gt (p : Params) (i : Fin 2)
    (x : ℝ × (ℝ × ℝ)) (hx : p.H / 2 < x.1) :
    p.inletProfile i x = 0 := by
  have hH : 0 < p.H := div_pos p.ageCut_pos p.ν_pos
  have hcut0 : p.cutStream i x = 0 := by
    unfold Params.cutStream
    simp [ageCutoff_eq_zero hH hx.le]
  have hev : ∀ᶠ y in 𝓝 x, p.H / 2 < y.1 :=
    (continuous_fst.tendsto x).eventually (lt_mem_nhds hx)
  have hfun : p.cutStream i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hev] with y hy
    unfold Params.cutStream
    simp [ageCutoff_eq_zero hH hy.le]
  have hfd : fderiv ℝ (p.cutStream i) x = 0 := by
    rw [hfun.fderiv_eq]
    simp
  have hdS : Axi.dS (p.cutStream i) x = 0 := by
    unfold Axi.dS
    rw [hfd]
    simp
  have hdQ : Axi.dQ (p.cutStream i) x = 0 := by
    unfold Axi.dQ
    rw [hfd]
    simp
  have hdE : Axi.dEta (p.cutStream i) x = 0 := by
    unfold Axi.dEta
    rw [hfd]
    simp
  simp [Params.inletProfile, Axi.ringStreamProfile, hdS, hdQ, hdE, hcut0]

theorem Efun_eq_zero_of_ϱ_lt (p : Params) (i : Fin 2) (τ : ℝ) (y : Space)
    (hy : Axi.ϱ y < p.R / (p.H / 2 + 1)) :
    p.Efun i (τ, y) = 0 := by
  have hH : 0 < p.H := div_pos p.ageCut_pos p.ν_pos
  have hH2 : 0 < p.H / 2 + 1 := by linarith
  have hinlet : p.inlet i τ y = 0 := by
    by_cases h0 : Axi.ϱ y = 0
    · simp [Params.inlet, Axi.Nv, Axi.age, h0]
    · have hϱpos : 0 < Axi.ϱ y := lt_of_le_of_ne (Axi.ϱ_nonneg y) (Ne.symm h0)
      have h1 : Axi.ϱ y * (p.H / 2 + 1) < p.R := (lt_div_iff₀ hH2).1 hy
      have h2 : (Axi.ϱ y * (p.H / 2 + 1)) ^ 2 < p.R ^ 2 :=
        pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
      have hbig : p.H / 2 < (Axi.chart p.R τ y).1 := by
        show p.H / 2 < Axi.age p.R y
        unfold Axi.age
        rw [lt_div_iff₀ (pow_pos hϱpos 2)]
        nlinarith [mul_nonneg (sq_nonneg (Axi.ϱ y))
          (by positivity : (0 : ℝ) ≤ (p.H / 2) ^ 2 + p.H / 2 + 1)]
      have hg : p.inletProfile i (Axi.chart p.R τ y) = 0 :=
        inletProfile_eq_zero_of_gt p i _ hbig
      simp [Params.inlet, Axi.Nv, hg]
  simp [Params.Efun, hinlet, realC]

theorem raw_contDiffOn_off_axis {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) {x | x.2 ∉ Axi.axis} := by
  have hN : ContDiffOn ℝ ∞
      (fun x : ℝ × Space => Axi.Nv p.R (merProfile p.R (trainStream p)) x.1 x.2)
      {x | x.2 ∉ Axi.axis} :=
    contDiffOn_Nv_pos p.R_pos.ne' (contDiffOn_merProfile (trainStream_contDiffOn_top hreg))
  exact hN.congr fun x hx => raw_eq_Nv_mer hreg x.1 hx

theorem pairF_L0T_add_convT_Efun {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    (i : Fin 2) (hE : Continuous (p.Efun i))
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period (fun x => L0T p.ν Φ x + convT p.raw Φ x) (p.Efun i) =
      pairF p.period (L0T p.ν Φ) (p.Efun i) + pairF p.period (convT p.raw Φ) (p.Efun i) := by
  have hH : 0 < p.H := div_pos p.ageCut_pos p.ν_pos
  have hH2 : 0 < p.H / 2 + 1 := by linarith
  exact pairF_add_convT_of_vanish_near_axis (raw_contDiffOn_off_axis hreg) hE
    (div_pos p.R_pos hH2) (Efun_eq_zero_of_ϱ_lt p i) hΦ

theorem contDiff_Efun_of_periodicStream {p : Params}
    (hper : ContDiff ℝ ∞ (periodicStream p.mode p.c)) (i : Fin 2) :
    ContDiff ℝ ∞ (p.Efun i) := by
  have hfro : ContDiff ℝ ∞ (p.frozenStream i) :=
    inletCD_frozenStream hper rfl i
  have hcut : ContDiff ℝ ∞ (p.cutStream i) := by
    unfold Params.cutStream
    exact ((contDiff_ageCutoff p.H).comp contDiff_fst).mul
      (hfro.comp contDiff_snd)
  have hB : ContDiff ℝ ∞ (p.inletProfile i) := by
    unfold Params.inletProfile
    exact inletCD_ringStreamProfile hcut
  have hinlet : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) :=
    NicePT.contDiff_Nv p.R_pos hB (s1 := p.H / 2) (inletProfile_eq_zero_of_gt p i)
  exact NicePT.contDiff_realC.comp hinlet

/-! ## 7. Main statement and theorem `row_ordRel` (`PartII-b:P3`, SP 2490-2498) -/

/-- **Statement of `PartII-b:P3`** (SP 2490-2498): if `rowOp Ke Ce y = J f` (`f ∈ p.Y`) and `Θ`
is a response operator as in `PartII-b:P2`, then `p.OrdRel (Θ y) (f : Yq p.period q0E)`. -/
def RowOrdRel : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp →
    (∀ i : Fin 2, Continuous (p.Efun i)) →
    ∀ (Ke : HpR p.c →L[ℝ] HpR p.c) (Ce : E2 →L[ℝ] HpR p.c), IsKop p Ke → IsCop p Ce →
      ∀ (Θ : RowSpace p.c →L[ℝ] p.Z),
        (∀ y : RowSpace p.c, p.coord (Θ y) = y.ofLp.2.ofLp) →
        (∀ (y : RowSpace p.c) (b : CProf),
          IsResponse p.ν p.c p.ε 0 bgp (toProf p.c y.ofLp.1) b →
            (∀ᵐ x : ℝ × Space, rep (p.wOf (Θ y)) x.1 x.2 = NvC p.R b x) ∧
              HasRep (p.wOf (Θ y)) (NvC p.R b)) →
        ∀ (J : p.Y →L[ℝ] HpR p.c),
          (∀ f : p.Y, ∀ᵐ x : ℝ × Space,
            rep (f : Yq p.period q0E) x.1 x.2 = NvC p.R (toProf p.c (J f)) x) →
          ∀ (y : RowSpace p.c) (f : p.Y),
            rowOp Ke Ce y = J f → p.OrdRel (Θ y) (f : Yq p.period q0E)

/-- **`PartII-b:P3`** (`row_ordRel`, SP 2490-2498): if `rowOp Ke Ce y = J f` (`f ∈ p.Y`) and
`Θ y` is as in `PartII-b:P2`, then `p.OrdRel (Θ y) (f : Yq p.period q0E)`. -/
theorem row_ordRel : RowOrdRel := by
  intro p d dm dp hreg hE Ke Ce hK hC Θ hcoord hrep J hJ y f hrow
  exact row_ordRel_of_split p hK hC hcoord hrep hJ
    (fun i Φ hΦ => pairF_L0T_add_convT_Efun hreg i (hE i) hΦ.1) y f hrow

/-- Specialization of `row_ordRel` to the concrete response operator `RespOp.thetaMap p hp1 hK`
from `PartII-b:P2` under `ContDiff ℝ ∞ (periodicStream p.mode p.c)`. -/
theorem row_ordRel_thetaMap {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    (hp1 : p.period ≤ 1)
    (hper : ContDiff ℝ ∞ (periodicStream p.mode p.c))
    {Ke : HpR p.c →L[ℝ] HpR p.c} {Ce : E2 →L[ℝ] HpR p.c}
    (hK : IsKop p Ke) (hC : IsCop p Ce)
    {J : p.Y →L[ℝ] HpR p.c}
    (hJ : ∀ f : p.Y, ∀ᵐ x : ℝ × Space,
      rep (f : Yq p.period q0E) x.1 x.2 = NvC p.R (toProf p.c (J f)) x)
    (y : RowSpace p.c) (f : p.Y) (hrow : rowOp Ke Ce y = J f) :
    p.OrdRel (thetaMap p hp1 hK y) (f : Yq p.period q0E) :=
  row_ordRel p d dm dp hreg
    (fun i => (contDiff_Efun_of_periodicStream hper i).continuous)
    Ke Ce hK hC (thetaMap p hp1 hK) (thetaMap_coord p hp1 hK) (thetaMap_hasRep p hp1 hK)
    J hJ y f hrow

end UnforcedLeray.Short.IIb

end
