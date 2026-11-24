import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2

/-!
# `GaussHeat`: the Gaussian heat equation for all iterated derivatives

Source `the November 2 reference manuscript`
3600-3610 (`∂_t G = ΔG`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.KPH

open UnforcedLeray.Short.IIIa

private abbrev UU : Set (ℝ × Space) := Ioi 0 ×ˢ univ

private lemma isOpen_UU : IsOpen UU := isOpen_Ioi.prod isOpen_univ

private lemma mem_UU {p : ℝ × Space} : p ∈ UU ↔ 0 < p.1 := by
  simp [UU]

private lemma sm_fd {g : ℝ × Space → ℝ} (hg : ContDiffOn ℝ ∞ g UU) :
    ContDiffOn ℝ ∞ (fderiv ℝ g) UU := hg.fderiv_of_isOpen isOpen_UU (by simp)

private lemma sm_fd_apply {g : ℝ × Space → ℝ} (hg : ContDiffOn ℝ ∞ g UU) (z : ℝ × Space) :
    ContDiffOn ℝ ∞ (fun q => fderiv ℝ g q z) UU :=
  (sm_fd hg).clm_apply contDiffOn_const

private lemma diffAt_of_sm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ × Space → F} (hg : ContDiffOn ℝ ∞ g UU) {q : ℝ × Space}
    (hq : q ∈ UU) : DifferentiableAt ℝ g q :=
  (hg.contDiffAt (isOpen_UU.mem_nhds hq)).differentiableAt (by simp)

private lemma fd_apply {g : ℝ × Space → ℝ} (hg : ContDiffOn ℝ ∞ g UU) {q : ℝ × Space}
    (hq : q ∈ UU) (z z' : ℝ × Space) :
    fderiv ℝ (fun q => fderiv ℝ g q z) q z' = fderiv ℝ (fderiv ℝ g) q z' z := by
  rw [fderiv_clm_apply (diffAt_of_sm (sm_fd hg) hq) (differentiableAt_const z)]
  simp

private lemma sym2 {g : ℝ × Space → ℝ} (hg : ContDiffOn ℝ ∞ g UU) {q : ℝ × Space}
    (hq : q ∈ UU) (z z' : ℝ × Space) :
    fderiv ℝ (fderiv ℝ g) q z z' = fderiv ℝ (fderiv ℝ g) q z' z :=
  (hg.contDiffAt (isOpen_UU.mem_nhds hq)).isSymmSndFDerivAt (by simp) z z'

private lemma fderiv_slice {φ : ℝ × Space → ℝ} {a : ℝ} {y : Space}
    (h : DifferentiableAt ℝ φ (a, y)) (w : Space) :
    fderiv ℝ φ (a, y) (0, w) = fderiv ℝ (fun z => φ (a, z)) y w := by
  have hs : HasFDerivAt (fun z : Space => (a, z))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const a y).prodMk (hasFDerivAt_id y)
  have := h.hasFDerivAt.comp y hs
  rw [show (fun z => φ (a, z)) = φ ∘ Prod.mk a from rfl, this.fderiv]
  simp

private lemma hasDerivAt_time {φ : ℝ × Space → ℝ} {a : ℝ} {y : Space}
    (h : DifferentiableAt ℝ φ (a, y)) :
    HasDerivAt (fun a' => φ (a', y)) (fderiv ℝ φ (a, y) (1, 0)) a := by
  have hs : HasDerivAt (fun a' : ℝ => (a', y)) ((1 : ℝ), (0 : Space)) a :=
    (hasDerivAt_id a).prodMk (hasDerivAt_const a y)
  exact h.hasFDerivAt.comp_hasDerivAt a hs

private lemma he_step {f : ℝ × Space → ℝ} (hf : ContDiffOn ℝ ∞ f UU)
    (he : ∀ p ∈ UU, fderiv ℝ f p (1, 0) = ∑ l : Fin 3,
      fderiv ℝ (fun q => fderiv ℝ f q (0, coordinateVector l)) p (0, coordinateVector l))
    (w : Space) : ∀ p ∈ UU, fderiv ℝ (fun q => fderiv ℝ f q (0, w)) p (1, 0) = ∑ l : Fin 3,
      fderiv ℝ (fun q => fderiv ℝ (fun q' => fderiv ℝ f q' (0, w)) q (0, coordinateVector l)) p
        (0, coordinateVector l) := by
  intro p hp
  have hU := isOpen_UU
  set hl : Fin 3 → ℝ × Space → ℝ := fun l q => fderiv ℝ f q (0, coordinateVector l) with hhl
  have hhls : ∀ l, ContDiffOn ℝ ∞ (hl l) UU := fun l => sm_fd_apply hf _
  have hmem : ∀ᶠ q in 𝓝 p, q ∈ UU := hU.mem_nhds hp
  -- LHS
  have h1 : fderiv ℝ (fun q => fderiv ℝ f q (0, w)) p (1, 0) =
      ∑ l : Fin 3, fderiv ℝ (fderiv ℝ (hl l)) p (0, w) (0, coordinateVector l) := by
    rw [fd_apply hf hp, sym2 hf hp, ← fd_apply hf hp]
    have hev : (fun q => fderiv ℝ f q (1, 0)) =ᶠ[𝓝 p]
        fun q => ∑ l : Fin 3, fderiv ℝ (hl l) q (0, coordinateVector l) :=
      hmem.mono fun q hq => he q hq
    rw [hev.fderiv_eq, fderiv_fun_sum]
    · simp only [sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      exact fd_apply (hhls l) hp _ _
    · intro l _
      exact diffAt_of_sm (sm_fd_apply (hhls l) _) hp
  have h2 : ∀ l : Fin 3, fderiv ℝ (fun q => fderiv ℝ (fun q' => fderiv ℝ f q' (0, w)) q
      (0, coordinateVector l)) p (0, coordinateVector l) =
      fderiv ℝ (fderiv ℝ (hl l)) p (0, w) (0, coordinateVector l) := by
    intro l
    have hev : (fun q => fderiv ℝ (fun q' => fderiv ℝ f q' (0, w)) q (0, coordinateVector l))
        =ᶠ[𝓝 p] fun q => fderiv ℝ (hl l) q (0, w) := by
      refine hmem.mono fun q hq => ?_
      have e1 : fderiv ℝ (fun q' => fderiv ℝ f q' (0, w)) q (0, coordinateVector l) =
          fderiv ℝ (fderiv ℝ f) q (0, coordinateVector l) (0, w) := by
        rw [fderiv_clm_apply (diffAt_of_sm (sm_fd hf) hq) (differentiableAt_const _)]
        simp
      have e2 : fderiv ℝ (hl l) q (0, w) = fderiv ℝ (fderiv ℝ f) q (0, w) (0, coordinateVector l) := by
        rw [hhl]
        rw [fderiv_clm_apply (diffAt_of_sm (sm_fd hf) hq) (differentiableAt_const _)]
        simp
      show fderiv ℝ (fun q' => fderiv ℝ f q' (0, w)) q (0, coordinateVector l) =
        fderiv ℝ (hl l) q (0, w)
      rw [e1, e2, sym2 hf hq]
    rw [hev.fderiv_eq]
    have := fd_apply (hhls l) hp (0, w) (0, coordinateVector l)
    rw [this, sym2 (hhls l) hp]
  rw [h1]
  exact Finset.sum_congr rfl fun l _ => (h2 l).symm

private def HH : ℝ × Space → ℝ := fun p => heatG p.1 p.2

private lemma sm_HH : ContDiffOn ℝ ∞ HH UU := by
  unfold HH heatG
  have h4 : ContDiffOn ℝ ∞ (fun p : ℝ × Space => 4 * Real.pi * p.1) UU :=
    (contDiffOn_const.mul contDiffOn_fst)
  refine ContDiffOn.mul ?_ ?_
  · exact h4.rpow_const_of_ne (fun p hp => by
      have := mem_UU.1 hp
      positivity)
  · refine Real.contDiff_exp.comp_contDiffOn ?_
    refine ContDiffOn.div ?_ (contDiffOn_const.mul contDiffOn_fst) (fun p hp => by
      have := mem_UU.1 hp
      positivity)
    exact ((contDiff_norm_sq ℝ).comp contDiff_snd).contDiffOn.neg

private lemma hasFDerivAt_heatG {a : ℝ} (ha : 0 < a) (y : Space) :
    HasFDerivAt (heatG a) ((-(heatG a y) / (2 * a)) • innerSL ℝ y) y := by
  have hn : HasFDerivAt (fun x : Space => ‖x‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hm := (hn.const_mul (-1 / (4 * a))).exp.const_mul ((4 * Real.pi * a) ^ (-3 / 2 : ℝ))
  have hf : heatG a = fun x : Space => (4 * Real.pi * a) ^ (-3 / 2 : ℝ) *
      Real.exp (-1 / (4 * a) * ‖x‖ ^ 2) := by
    funext x; unfold heatG; congr 2; ring
  rw [hf]
  refine hm.congr_fderiv ?_
  ext w
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  generalize Real.exp (-1 / (4 * a) * ‖y‖ ^ 2) = E
  generalize (4 * Real.pi * a) ^ (-3 / 2 : ℝ) = R
  field_simp
  ring

private lemma hasDerivAt_heatG_time {a : ℝ} (ha : 0 < a) (y : Space) :
    HasDerivAt (fun a' => heatG a' y)
      ((-3 / (2 * a) + ‖y‖ ^ 2 / (4 * a ^ 2)) * heatG a y) a := by
  have hu : HasDerivAt (fun a' : ℝ => 4 * Real.pi * a') (4 * Real.pi) a := by
    simpa using (hasDerivAt_id a).const_mul (4 * Real.pi)
  have h1 := hu.rpow_const (p := (-3 / 2 : ℝ)) (Or.inl (by positivity))
  have hv : HasDerivAt (fun a' : ℝ => 4 * a') 4 a := by
    simpa using (hasDerivAt_id a).const_mul (4 : ℝ)
  have h2 := ((hasDerivAt_const a (-‖y‖ ^ 2)).div hv (by positivity)).exp
  have h3 := h1.mul h2
  refine h3.congr_deriv ?_
  have hpos : (0 : ℝ) < 4 * Real.pi * a := by positivity
  rw [show (-3 / 2 : ℝ) - 1 = -3 / 2 + (-1) by norm_num, Real.rpow_add hpos, Real.rpow_neg_one]
  simp only [Pi.div_apply, heatG]
  generalize Real.exp (-‖y‖ ^ 2 / (4 * a)) = E
  generalize (4 * Real.pi * a) ^ (-3 / 2 : ℝ) = R
  field_simp
  ring

private lemma inner_coord (y : Space) (l : Fin 3) : inner ℝ y (coordinateVector l) = y l := by
  simp [coordinateVector, EuclideanSpace.inner_single_right]

private lemma lapG {a : ℝ} (ha : 0 < a) (y : Space) :
    ∑ l : Fin 3, fderiv ℝ (fun y' => fderiv ℝ (heatG a) y' (coordinateVector l)) y
      (coordinateVector l) = (-3 / (2 * a) + ‖y‖ ^ 2 / (4 * a ^ 2)) * heatG a y := by
  have hterm : ∀ l : Fin 3, fderiv ℝ (fun y' => fderiv ℝ (heatG a) y' (coordinateVector l)) y
      (coordinateVector l) = (-1 / (2 * a)) * (heatG a y - (y l) ^ 2 * heatG a y / (2 * a)) := by
    intro l
    have hfun : (fun y' => fderiv ℝ (heatG a) y' (coordinateVector l)) =
        fun y' : Space => (-1 / (2 * a)) * (heatG a y' * (EuclideanSpace.proj l : Space →L[ℝ] ℝ) y') := by
      funext y'
      rw [(hasFDerivAt_heatG ha y').fderiv]
      have hp : (EuclideanSpace.proj l : Space →L[ℝ] ℝ) y' = y' l := rfl
      simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, inner_coord, hp]
      ring
    rw [hfun]
    have hd := (((hasFDerivAt_heatG ha y).mul (EuclideanSpace.proj l : Space →L[ℝ] ℝ).hasFDerivAt).const_mul
      (-1 / (2 * a)))
    rw [show (fun y' : Space => -1 / (2 * a) * (heatG a y' * (EuclideanSpace.proj l : Space →L[ℝ] ℝ) y'))
      = (fun y => -1 / (2 * a) * (heatG a * ⇑(EuclideanSpace.proj l : Space →L[ℝ] ℝ)) y) from rfl, hd.fderiv]
    have h1 : (EuclideanSpace.proj l : Space →L[ℝ] ℝ) (coordinateVector l) = 1 := by
      simp [coordinateVector]
    have hpy : (EuclideanSpace.proj l : Space →L[ℝ] ℝ) y = y l := rfl
    simp only [ContinuousLinearMap.add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
      inner_coord, h1, hpy]
    ring
  rw [Finset.sum_congr rfl fun l _ => hterm l]
  have hn : ‖y‖ ^ 2 = ∑ l : Fin 3, (y l) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  have hn3 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by rw [hn, Fin.sum_univ_three]
  rw [Fin.sum_univ_three, hn3]
  field_simp
  ring

private lemma he_base : ∀ p ∈ UU, fderiv ℝ HH p (1, 0) = ∑ l : Fin 3,
    fderiv ℝ (fun q => fderiv ℝ HH q (0, coordinateVector l)) p (0, coordinateVector l) := by
  rintro ⟨a, y⟩ hp
  have ha : 0 < a := mem_UU.1 hp
  have hd : DifferentiableAt ℝ HH (a, y) := diffAt_of_sm sm_HH hp
  have h1 : fderiv ℝ HH (a, y) (1, 0) = (-3 / (2 * a) + ‖y‖ ^ 2 / (4 * a ^ 2)) * heatG a y := by
    have := hasDerivAt_time hd
    exact this.unique (hasDerivAt_heatG_time ha y)
  rw [h1, ← lapG ha y]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hdl : DifferentiableAt ℝ (fun q => fderiv ℝ HH q (0, coordinateVector l)) (a, y) :=
    diffAt_of_sm (sm_fd_apply sm_HH _) hp
  rw [fderiv_slice hdl]
  congr 2
  funext z
  have hz : ((a, z) : ℝ × Space) ∈ UU := hp
  rw [fderiv_slice (diffAt_of_sm sm_HH hz)]
  rfl

private def FF : (n : ℕ) → (Fin n → Space) → ℝ × Space → ℝ
  | 0, _ => HH
  | n + 1, v => fun p => fderiv ℝ (FF n (Fin.tail v)) p (0, v 0)

private lemma sm_FF : ∀ (n : ℕ) (v : Fin n → Space), ContDiffOn ℝ ∞ (FF n v) UU
  | 0, _ => sm_HH
  | n + 1, v => sm_fd_apply (sm_FF n (Fin.tail v)) _

private lemma he_FF : ∀ (n : ℕ) (v : Fin n → Space), ∀ p ∈ UU, fderiv ℝ (FF n v) p (1, 0) =
    ∑ l : Fin 3, fderiv ℝ (fun q => fderiv ℝ (FF n v) q (0, coordinateVector l)) p
      (0, coordinateVector l)
  | 0, _ => he_base
  | n + 1, v => he_step (sm_FF n (Fin.tail v)) (he_FF n (Fin.tail v)) (v 0)

private lemma slice_FF {n : ℕ} (v : Fin n → Space) {a : ℝ} (ha : 0 < a) (z w : Space) :
    fderiv ℝ (FF n v) (a, z) (0, w) = fderiv ℝ (fun z' => FF n v (a, z')) z w :=
  fderiv_slice (diffAt_of_sm (sm_FF n v) (mem_UU.2 ha)) w

private lemma FF_eq : ∀ (n : ℕ) (v : Fin n → Space) {a : ℝ}, 0 < a →
    (fun z => FF n v (a, z)) = fun z => iteratedFDeriv ℝ n (heatG a) z v
  | 0, v, a, _ => by
    funext z
    simp [FF, HH]
  | n + 1, v, a, ha => by
    funext z
    have ih := FF_eq n (Fin.tail v) ha
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (heatG a)) :=
      (contDiff_heatG ha).differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top n)
    show fderiv ℝ (FF n (Fin.tail v)) (a, z) (0, v 0) = _
    rw [slice_FF _ ha, ih, iteratedFDeriv_succ_apply_left,
      fderiv_continuousMultilinear_apply_const_apply (hdiff z)]

theorem gaussHeat : UnforcedLeray.Short.PartIIIb.Concrete.KPH.GaussHeat := by
  constructor
  · intro t ht k x
    set v : Fin 1 → Space := fun _ => coordinateVector k with hv
    have hp : ((t, x) : ℝ × Space) ∈ UU := mem_UU.2 ht
    have hd := hasDerivAt_time (diffAt_of_sm (sm_FF 1 v) hp)
    have hev : (fun t' => fderiv ℝ (fun y => heatG t' y) x (coordinateVector k)) =ᶠ[𝓝 t]
        fun t' => FF 1 v (t', x) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show (0:ℝ) < t from ht)] with t' ht'
      show _ = fderiv ℝ (FF 0 (Fin.tail v)) (t', x) (0, v 0)
      rw [slice_FF _ ht']
      rfl
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [he_FF 1 v _ hp]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hdl : DifferentiableAt ℝ (fun q => fderiv ℝ (FF 1 v) q (0, coordinateVector l)) (t, x) :=
      diffAt_of_sm (sm_fd_apply (sm_FF 1 v) _) hp
    rw [fderiv_slice hdl]
    congr 2
    funext z
    rw [slice_FF _ ht]
    show fderiv ℝ (fun z' => fderiv ℝ (FF 0 (Fin.tail v)) (t, z') (0, v 0)) z (coordinateVector l) = _
    have : (fun z' => fderiv ℝ (FF 0 (Fin.tail v)) (t, z') (0, v 0)) =
        fun y' => fderiv ℝ (heatG t) y' (coordinateVector k) := by
      funext z'
      rw [slice_FF _ ht]
      rfl
    rw [this]
  · intro n a ha x v
    have hp : ((a, x) : ℝ × Space) ∈ UU := mem_UU.2 ha
    have hd := hasDerivAt_time (diffAt_of_sm (sm_FF n v) hp)
    have hev : (fun a' => iteratedFDeriv ℝ n (heatG a') x v) =ᶠ[𝓝 a]
        fun a' => FF n v (a', x) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show (0:ℝ) < a from ha)] with a' ha'
      exact (congrFun (FF_eq n v ha') x).symm
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [he_FF n v _ hp]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := congrFun (FF_eq (n + 2) (Fin.cons (coordinateVector l) (Fin.cons (coordinateVector l) v)) ha) x
    rw [← this]
    simp [FF]
