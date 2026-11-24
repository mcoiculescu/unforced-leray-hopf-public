import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.IteratedQuadDerivY.Leibniz
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.SliceBridge
import UnforcedLeray.Lib.ConvIneq.HolderExponents

/-!
# Word-indexed derivatives of `u = e + w` (`PartII-b:S2/1/4`, helper)

Source of record: `the November 2 reference manuscript`,
lines 2552-2559.

* `dWord l v`: the iterated distributional derivative of `v ∈ Y_q₀` along the word `l` (head
  first), built from the selector `dSel` (any weak derivative; unique by `hasPhaseOp_unique`).
  `tower_hasPhaseOp`: a `HasPhaseGradTower` of height `m` makes every step of length `≤ m`
  a genuine weak derivative; `dWord_ofFn_of_iterated`: `dWord` agrees with any
  `IsIteratedPhaseGrad` family.
* `eWord l G`: the classical iterated derivative of a smooth field along `l`, with
  `eWord (List.ofFn β) G = iterDyRev β G` and the slice bound by `iteratedFDeriv`.
* Integrability helpers: `(1+|y|)^{-1} ∈ L^{2q₀}(ℝ³)`, the Hölder triple `(2q₀, 2q₀, q₀)`, and
  `exists_Yq_of_field` (a measurable periodic `L^{q₀}` field on the cell represents an element of
  `Y_{q₀}`, as in `gEQYq2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

namespace IterQuadSub

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Cons.C03.Concrete (phaseInt phaseCell pairF advT rep rep_add_period
  stronglyMeasurable_rep)
open scoped ContDiff ENNReal

/-! ### Distributional words -/

section DWord

variable {P : ℝ} [Fact (0 < P)]

open Classical in
/-- A selected weak `y_j`-derivative (`0` if there is none). -/
def dSel (j : Fin 3) (v : Yq P UnforcedLeray.B0412.q0E) : Yq P UnforcedLeray.B0412.q0E :=
  if h : ∃ v' : Yq P UnforcedLeray.B0412.q0E, HasPhaseOp (fun Φ => -dy j Φ) v v' then h.choose
  else 0

theorem dSel_spec {j : Fin 3} {v v' : Yq P UnforcedLeray.B0412.q0E}
    (h : HasPhaseOp (fun Φ => -dy j Φ) v v') : dSel j v = v' := by
  have hex : ∃ v' : Yq P UnforcedLeray.B0412.q0E, HasPhaseOp (fun Φ => -dy j Φ) v v' := ⟨v', h⟩
  classical
  unfold dSel
  rw [dif_pos hex]
  exact UnforcedLeray.B0411.hasPhaseOp_unique hex.choose_spec h

/-- The iterated selected derivative along a word (head first). -/
def dWord (l : List (Fin 3)) (v : Yq P UnforcedLeray.B0412.q0E) : Yq P UnforcedLeray.B0412.q0E :=
  l.foldl (fun u j => dSel j u) v

theorem dWord_append (l : List (Fin 3)) (j : Fin 3) (v : Yq P UnforcedLeray.B0412.q0E) :
    dWord (l ++ [j]) v = dSel j (dWord l v) := by
  simp [dWord, List.foldl_append]

theorem tower_hasPhaseOp :
    ∀ (l : List (Fin 3)) (m : ℕ) (v : Yq P UnforcedLeray.B0412.q0E),
      HasPhaseGradTower P UnforcedLeray.B0412.q0E m v → l.length ≤ m →
      ∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (dWord l v) (dWord (l ++ [j]) v)
  | [], m, v, hT, _, j => by
      have hex : ∃ v' : Fin 3 → Yq P UnforcedLeray.B0412.q0E,
          ∀ l : Fin 3, HasPhaseOp (fun Φ => -dy l Φ) v (v' l) := by
        cases m with
        | zero => exact hT
        | succ m => obtain ⟨v', hv', -⟩ := hT; exact ⟨v', hv'⟩
      obtain ⟨v', hv'⟩ := hex
      show HasPhaseOp (fun Φ => -dy j Φ) v (dSel j v)
      rw [dSel_spec (hv' j)]
      exact hv' j
  | b :: l, m, v, hT, hl, j => by
      cases m with
      | zero => simp at hl
      | succ m =>
          obtain ⟨v', hv', hT'⟩ := hT
          have hb : dSel b v = v' b := dSel_spec (hv' b)
          have hT'' : HasPhaseGradTower P UnforcedLeray.B0412.q0E m (dSel b v) := by
            rw [hb]; exact hT' b
          have hl' : l.length ≤ m := by simp only [List.length_cons] at hl; omega
          exact tower_hasPhaseOp l m (dSel b v) hT'' hl' j

theorem dWord_ofFn_of_iterated :
    ∀ (n : ℕ) (u : Yq P UnforcedLeray.B0412.q0E)
      (g : (Fin n → Fin 3) → Yq P UnforcedLeray.B0412.q0E),
      IsIteratedPhaseGrad P UnforcedLeray.B0412.q0E n u g →
      ∀ α : Fin n → Fin 3, dWord (List.ofFn α) u = g α
  | 0, u, g, hg, α => by
      have hα : α = Fin.elim0 := Subsingleton.elim _ _
      subst hα
      simp only [List.ofFn_zero]
      exact hg.symm
  | n + 1, u, g, ⟨g₀, hg₀, hop⟩, α => by
      rw [ofFn_succ_eq α, dWord_append, dWord_ofFn_of_iterated n u g₀ hg₀ (Fin.init α),
        dSel_spec (hop (Fin.init α) (α (Fin.last n))), Fin.snoc_init_self]

end DWord

/-! ### Classical words -/

section EWord

/-- The classical iterated derivative along a word (head first). -/
def eWord (l : List (Fin 3)) (G : ℝ × UnforcedLeray.Space → CVec3) :
    ℝ × UnforcedLeray.Space → CVec3 :=
  l.foldl (fun F j => dy j F) G

theorem eWord_append (l : List (Fin 3)) (j : Fin 3) (G : ℝ × UnforcedLeray.Space → CVec3) :
    eWord (l ++ [j]) G = dy j (eWord l G) := by
  simp [eWord, List.foldl_append]

theorem contDiff_eWord :
    ∀ (l : List (Fin 3)) {G : ℝ × UnforcedLeray.Space → CVec3}, ContDiff ℝ ∞ G →
      ContDiff ℝ ∞ (eWord l G)
  | [], _, hG => hG
  | j :: l, G, hG => contDiff_eWord l (G := dy j G) (contDiff_dyT hG j)

theorem eWord_periodic {P : ℝ} :
    ∀ (l : List (Fin 3)) {G : ℝ × UnforcedLeray.Space → CVec3},
      (∀ x : ℝ × UnforcedLeray.Space, G (x.1 + P, x.2) = G x) →
      ∀ x : ℝ × UnforcedLeray.Space, eWord l G (x.1 + P, x.2) = eWord l G x
  | [], _, hG => hG
  | j :: l, G, hG => eWord_periodic l (G := dy j G) (fun x => dy_periodic' hG j x)

theorem eWord_ofFn (G : ℝ × UnforcedLeray.Space → CVec3) :
    ∀ {n : ℕ} (β : Fin n → Fin 3), eWord (List.ofFn β) G = iterDyRev β G
  | 0, β => by simp [eWord, iterDyRev]
  | n + 1, β => by
      rw [ofFn_succ_eq β, eWord_append, eWord_ofFn G (Fin.init β)]
      rfl

theorem eWord_eq_iterDyRev (G : ℝ × UnforcedLeray.Space → CVec3) (l : List (Fin 3)) :
    eWord l G = iterDyRev l.get G := by
  conv_lhs => rw [← List.ofFn_get l]
  exact eWord_ofFn G l.get

/-- Slice identity for `iterDyRev` of a smooth field (`RawIterEnvSub.iterDyRev_eq_slice` with
`U = univ`). -/
theorem iterDyRev_eq_slice_univ {G : ℝ × UnforcedLeray.Space → CVec3} (hG : ContDiff ℝ ∞ G) :
    ∀ {m : ℕ} (β : Fin m → Fin 3) (a : ℝ) (y : UnforcedLeray.Space),
      iterDyRev β G (a, y) =
        iteratedFDeriv ℝ m (fun w => G (a, w)) y
          (fun i => UnforcedLeray.coordinateVector (β (Fin.rev i)))
  | 0, β, a, y => by
      simp [iterDyRev, iteratedFDeriv_zero_apply]
  | m + 1, β, a, y => by
      have hU : IsOpen (univ : Set (ℝ × UnforcedLeray.Space)) := isOpen_univ
      have hGU : ContDiffOn ℝ ∞ G univ := hG.contDiffOn
      have hH : ContDiffOn ℝ ∞ (iterDyRev (Fin.init β) G) univ :=
        (IterDiffEqSub.contDiff_iterDyRev (Fin.init β) hG).contDiffOn
      have hS : ContDiff ℝ ∞ (fun w => G (a, w)) :=
        hG.comp (contDiff_const.prodMk contDiff_id)
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ m (fun w => G (a, w))) y :=
        (hS.contDiffAt).differentiableAt_iteratedFDeriv
          (by exact_mod_cast ENat.natCast_lt_top m)
      have hev : (fun w => iterDyRev (Fin.init β) G (a, w)) =
          fun w => iteratedFDeriv ℝ m (fun w => G (a, w)) w
            (fun i => UnforcedLeray.coordinateVector (Fin.init β (Fin.rev i))) :=
        funext fun w => iterDyRev_eq_slice_univ hG (Fin.init β) a w
      have htail : Fin.tail (fun i : Fin (m + 1) =>
          UnforcedLeray.coordinateVector (β (Fin.rev i))) =
          fun i => UnforcedLeray.coordinateVector (Fin.init β (Fin.rev i)) := by
        funext i
        simp [Fin.tail, Fin.init, Fin.rev_succ]
      have h0 : UnforcedLeray.coordinateVector (β (Fin.rev (0 : Fin (m + 1)))) =
          UnforcedLeray.coordinateVector (β (Fin.last m)) := by
        simp [Fin.rev_zero]
      show dy (β (Fin.last m)) (iterDyRev (Fin.init β) G) (a, y) = _
      rw [sb_slice_dy hU hH a y (mem_univ _), hev, hdiff.iteratedFDeriv_succ_apply_left', htail]
      exact congrArg _ h0.symm

theorem norm_eWord_le_slice {G : ℝ × UnforcedLeray.Space → CVec3} (hG : ContDiff ℝ ∞ G)
    (l : List (Fin 3)) (a : ℝ) (y : UnforcedLeray.Space) :
    ‖eWord l G (a, y)‖ ≤ ‖iteratedFDeriv ℝ l.length (fun w => G (a, w)) y‖ := by
  rw [eWord_eq_iterDyRev, iterDyRev_eq_slice_univ hG l.get a y]
  exact sb_opnorm _ _ (fun i => sb_norm_coord _)

end EWord

/-! ### The complexification as a continuous linear map -/

/-- `realC` as an `ℝ`-linear continuous map. -/
def realCL : UnforcedLeray.Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := UnforcedLeray.B0412.realC
      map_add' := fun x y => by
        ext i
        simp [UnforcedLeray.B0412.realC_apply]
      map_smul' := fun c x => by
        ext i
        simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul] }

theorem realCL_apply (x : UnforcedLeray.Space) : realCL x = UnforcedLeray.B0412.realC x := rfl

theorem norm_realCL_le : ‖realCL‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, realCL_apply]
  have h : ‖UnforcedLeray.B0412.realC x‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp only [UnforcedLeray.B0412.realC_apply, Complex.norm_real]
  exact h.le

/-! ### Integrability helpers -/

theorem two_mul_q0E : 2 * UnforcedLeray.B0412.q0E = ENNReal.ofReal (11 / 2) := by
  rw [show (11 / 2 : ℝ) = 2 * (11 / 4) by norm_num, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_ofNat]
  rfl

instance holderTriple_two_q0E :
    ENNReal.HolderTriple (2 * UnforcedLeray.B0412.q0E) (2 * UnforcedLeray.B0412.q0E)
      UnforcedLeray.B0412.q0E := by
  have h := UnforcedLeray.Conv.holderTriple_ofReal (p := 11 / 2) (q := 11 / 2) (r := 11 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [two_mul_q0E]
  exact h

theorem memLp_one_add_norm_inv :
    MemLp (fun y : UnforcedLeray.Space => (1 + ‖y‖) ^ (-(1 : ℝ))) (2 * UnforcedLeray.B0412.q0E)
      volume := by
  have hm : AEStronglyMeasurable (fun y : UnforcedLeray.Space => (1 + ‖y‖) ^ (-(1 : ℝ)))
      volume := (by fun_prop : Measurable fun y : UnforcedLeray.Space =>
        (1 + ‖y‖) ^ (-(1 : ℝ))).aestronglyMeasurable
  have h0 : 2 * UnforcedLeray.B0412.q0E ≠ 0 := by rw [two_mul_q0E]; simp
  have ht : 2 * UnforcedLeray.B0412.q0E ≠ ⊤ := by rw [two_mul_q0E]; simp
  rw [← integrable_norm_rpow_iff hm h0 ht]
  have hr : (2 * UnforcedLeray.B0412.q0E).toReal = 11 / 2 := by
    rw [two_mul_q0E, ENNReal.toReal_ofReal (by norm_num)]
  have hfin : ((Module.finrank ℝ UnforcedLeray.Space : ℕ) : ℝ) < 11 / 2 := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  refine (integrable_one_add_norm hfin).congr (ae_of_all _ fun y => ?_)
  have hy : 0 ≤ 1 + ‖y‖ := by positivity
  simp only [hr]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hy _), ← Real.rpow_mul hy]
  norm_num

/-- A field on the cell bounded off the axis by `B (1+|y|)^{-1}` is in `L^{2q₀}` of the cell. -/
theorem memLp_cell_of_inv_bound {P : ℝ} {f : ℝ × UnforcedLeray.Space → CVec3}
    (hf : AEStronglyMeasurable f (cellMeasure P)) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ (τ : ℝ) (y : UnforcedLeray.Space), y ∉ UnforcedLeray.Axi.axis →
      ‖f (τ, y)‖ * (1 + ‖y‖) ≤ B) :
    MemLp f (2 * UnforcedLeray.B0412.q0E) (cellMeasure P) := by
  have G := (memLp_one_add_norm_inv.const_mul B).comp_snd (volume.restrict (Ioc (0 : ℝ) P))
  refine G.of_le hf ?_
  have hax : ∀ᵐ x ∂(cellMeasure P), x.2 ∉ UnforcedLeray.Axi.axis :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd
      UnforcedLeray.Axi.ae_not_mem_axis
  filter_upwards [hax] with x hx
  have hy : 0 < 1 + ‖x.2‖ := by positivity
  have h1 := h x.1 x.2 hx
  rw [Real.norm_of_nonneg (mul_nonneg hB (Real.rpow_nonneg hy.le _)), Real.rpow_neg_one]
  rw [← div_eq_mul_inv, le_div_iff₀ hy]
  exact h1

/-- A field on the cell bounded off the axis by `B (1+|y|)^{-1}` is in `L^∞` of the cell. -/
theorem memLp_top_cell_of_inv_bound {P : ℝ} {f : ℝ × UnforcedLeray.Space → CVec3}
    (hf : AEStronglyMeasurable f (cellMeasure P)) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ (τ : ℝ) (y : UnforcedLeray.Space), y ∉ UnforcedLeray.Axi.axis →
      ‖f (τ, y)‖ * (1 + ‖y‖) ≤ B) :
    MemLp f ∞ (cellMeasure P) := by
  refine memLp_top_of_bound hf B ?_
  have hax : ∀ᵐ x ∂(cellMeasure P), x.2 ∉ UnforcedLeray.Axi.axis :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd
      UnforcedLeray.Axi.ae_not_mem_axis
  filter_upwards [hax] with x hx
  have h1 := h x.1 x.2 hx
  have h2 : ‖f x‖ ≤ ‖f x‖ * (1 + ‖x.2‖) := le_mul_of_one_le_right (norm_nonneg _) (by
    have := norm_nonneg x.2; linarith)
  exact h2.trans h1

/-- A strongly measurable, `P`-periodic field in `L^{q₀}` of the cell represents an element of
`Y_{q₀}` (the closing step of `gEQYq2`). -/
theorem exists_Yq_of_field {P : ℝ} [Fact (0 < P)] (F : ℝ × UnforcedLeray.Space → CVec3)
    (hSM : StronglyMeasurable F) (hper : ∀ x : ℝ × UnforcedLeray.Space, F (x.1 + P, x.2) = F x)
    (hL : MemLp F UnforcedLeray.B0412.q0E (cellMeasure P)) :
    ∃ Fq : Yq P UnforcedLeray.B0412.q0E, ∀ Φ, IsPhaseTest P Φ →
      phasePair P UnforcedLeray.B0412.q0E Φ Fq = pairF P Φ F := by
  have hq0 : UnforcedLeray.B0412.q0E ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ UnforcedLeray.B0412.q0E))
  have hfin : ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y, ‖F (τ, y)‖ₑ ^
      UnforcedLeray.B0412.q0E.toReal < ⊤ := by
    have h1 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0
      UnforcedLeray.B0412.q0E_ne_top).1 hL.eLpNorm_lt_top
    have hae : AEMeasurable (fun x => ‖F x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal)
        (cellMeasure P) := (hL.aestronglyMeasurable.enorm).pow_const _
    have h2 : ∫⁻ x, ‖F x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal ∂(cellMeasure P) =
        ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y, ‖F (τ, y)‖ₑ ^ UnforcedLeray.B0412.q0E.toReal :=
      lintegral_prod _ hae
    rwa [← h2]
  obtain ⟨Fq, hF⟩ := UnforcedLeray.Short.PartIIa.periodicFieldToYq_proof
    UnforcedLeray.B0412.q0E (by simp [UnforcedLeray.B0412.q0E]) P _ hSM
    (ae_of_all _ fun τ => ae_of_all _ fun y => hper (τ, y)) hfin
  refine ⟨Fq, fun Φ hΦ => ?_⟩
  rw [UnforcedLeray.Cons.C03.Concrete.phasePair_eq_pairF_rep hΦ Fq]
  unfold pairF phaseInt
  congr 1
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  have h2 : ∀ᵐ τ : ℝ, (fun y => rep Fq τ y) =ᵐ[volume] (fun y => F (τ, y)) := by
    filter_upwards [hF.slice] with τ hτ
    exact (UnforcedLeray.Cons.C03.Concrete.rep_slice Fq τ).trans hτ.symm
  filter_upwards [h2] with τ hτ
  exact integral_congr_ae (by filter_upwards [hτ] with y hy; simp only [hy])

end IterQuadSub

end UnforcedLeray.Short.IIb
