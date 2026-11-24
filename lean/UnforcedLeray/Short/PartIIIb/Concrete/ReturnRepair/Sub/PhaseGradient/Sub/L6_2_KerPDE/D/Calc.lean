import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_2

/-!
# Calculus on the joint kernel `P(t,x) = K_t(x)` (support for `GkerHasDerivH`)

Source `the November 2 reference manuscript`
3598-3610, 3800-3807.  With `P` jointly `C³` on `{t > 0}`: slice derivatives, symmetry of the
second and third derivatives, the heat equation and the Euler form for `D_k = ∂_k P`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.KerCalc

open UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete

/-- The half space `{t > 0}`. -/
def U : Set (ℝ × Space) := {p | 0 < p.1}

lemma isOpen_U : IsOpen U := isOpen_lt continuous_const continuous_fst

lemma mem_U {p : ℝ × Space} (hp : 0 < p.1) : p ∈ U := hp

lemma eval_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × Space → ((ℝ × Space) →L[ℝ] F)} {p : ℝ × Space} (hf : DifferentiableAt ℝ f p)
    (a w : ℝ × Space) :
    fderiv ℝ (fun q => f q a) p w = fderiv ℝ f p w a := by
  have h := (ContinuousLinearMap.apply ℝ F a).hasFDerivAt.comp p hf.hasFDerivAt
  have h2 : (fun q => f q a) = (ContinuousLinearMap.apply ℝ F a) ∘ f := rfl
  rw [h2, h.fderiv]; rfl

lemma eval_differentiable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × Space → ((ℝ × Space) →L[ℝ] F)} {p : ℝ × Space} (hf : DifferentiableAt ℝ f p)
    (a : ℝ × Space) : DifferentiableAt ℝ (fun q => f q a) p :=
  (ContinuousLinearMap.apply ℝ F a).differentiableAt.comp p hf

lemma slice_fderiv {f : ℝ × Space → ℝ} {τ : ℝ} {x : Space} (hf : DifferentiableAt ℝ f (τ, x))
    (w : Space) : fderiv ℝ (fun y => f (τ, y)) x w = fderiv ℝ f (τ, x) (0, w) := by
  have hg : HasFDerivAt (fun y : Space => (τ, y))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) x :=
    (hasFDerivAt_const τ x).prodMk (hasFDerivAt_id x)
  have h := HasFDerivAt.comp x (g := f) (by simpa using hf.hasFDerivAt) hg
  have h' : HasFDerivAt (fun y : Space => f (τ, y)) _ x := h
  rw [h'.fderiv]; simp

lemma time_deriv {f : ℝ × Space → ℝ} {τ : ℝ} {x : Space} (hf : DifferentiableAt ℝ f (τ, x)) :
    deriv (fun s => f (s, x)) τ = fderiv ℝ f (τ, x) (1, 0) := by
  have hg : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Space)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ x)
  have h := (show HasFDerivAt f (fderiv ℝ f (τ, x)) (τ, x) from hf.hasFDerivAt).comp_hasDerivAt τ hg
  exact h.deriv

section Generic

variable {P : ℝ × Space → ℝ} (hP : ContDiffOn ℝ 3 P U)
include hP

lemma diff0 {q : ℝ × Space} (hq : q ∈ U) : DifferentiableAt ℝ P q :=
  (hP.contDiffAt (isOpen_U.mem_nhds hq)).differentiableAt (by norm_num)

lemma diff1 {q : ℝ × Space} (hq : q ∈ U) : DifferentiableAt ℝ (fderiv ℝ P) q := by
  have := hP.fderiv_of_isOpen (m := 2) isOpen_U (by norm_num)
  exact (this.contDiffAt (isOpen_U.mem_nhds hq)).differentiableAt (by norm_num)

lemma diff2 {q : ℝ × Space} (hq : q ∈ U) : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ P)) q := by
  have h1 := hP.fderiv_of_isOpen (m := 2) isOpen_U (by norm_num)
  have h2 := h1.fderiv_of_isOpen (m := 1) isOpen_U (by norm_num)
  exact (h2.contDiffAt (isOpen_U.mem_nhds hq)).differentiableAt (by norm_num)

lemma cd2 {q : ℝ × Space} (hq : q ∈ U) : ContDiffAt ℝ 2 (fderiv ℝ P) q :=
  (hP.fderiv_of_isOpen (m := 2) isOpen_U (by norm_num)).contDiffAt (isOpen_U.mem_nhds hq)

lemma symm1 {q : ℝ × Space} (hq : q ∈ U) (a b : ℝ × Space) :
    fderiv ℝ (fderiv ℝ P) q a b = fderiv ℝ (fderiv ℝ P) q b a :=
  ((hP.contDiffAt (isOpen_U.mem_nhds hq)).isSymmSndFDerivAt
    (by simp [minSmoothness_of_isRCLikeNormedField] <;> norm_num)) a b

lemma symm2 {p : ℝ × Space} (hp : p ∈ U) (w a b : ℝ × Space) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ P)) p w a b = fderiv ℝ (fderiv ℝ (fderiv ℝ P)) p a w b := by
  have h := ((cd2 hP hp).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField] <;> norm_num)) w a
  exact congrArg (fun L => L b) h

lemma symm3 {p : ℝ × Space} (hp : p ∈ U) (w a b : ℝ × Space) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ P)) p w a b = fderiv ℝ (fderiv ℝ (fderiv ℝ P)) p w b a := by
  have hM := diff2 hP hp
  have key : ∀ a b : ℝ × Space, fderiv ℝ (fun q => fderiv ℝ (fderiv ℝ P) q a b) p w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ P)) p w a b := by
    intro a b
    have h1 : DifferentiableAt ℝ (fun q => fderiv ℝ (fderiv ℝ P) q a) p := eval_differentiable hM a
    rw [eval_apply h1 b w, eval_apply hM a w]
  have heq : (fun q => fderiv ℝ (fderiv ℝ P) q a b) =ᶠ[nhds p]
      (fun q => fderiv ℝ (fderiv ℝ P) q b a) := by
    filter_upwards [isOpen_U.mem_nhds hp] with q hq using symm1 hP hq a b
  rw [← key a b, ← key b a, heq.fderiv_eq]

lemma fderiv_Dl {q : ℝ × Space} (hq : q ∈ U) (v a : ℝ × Space) :
    fderiv ℝ (fun q' => fderiv ℝ P q' v) q a = fderiv ℝ (fderiv ℝ P) q a v :=
  eval_apply (diff1 hP hq) v a

end Generic

lemma third_eval {P : ℝ × Space → ℝ} (hP : ContDiffOn ℝ 3 P U) {p : ℝ × Space} (hp : p ∈ U)
    (w a b : ℝ × Space) :
    fderiv ℝ (fun q => fderiv ℝ (fderiv ℝ P) q a b) p w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ P)) p w a b := by
  have hM := diff2 hP hp
  have h1 : DifferentiableAt ℝ (fun q => fderiv ℝ (fderiv ℝ P) q a) p := eval_differentiable hM a
  rw [eval_apply h1 b w, eval_apply hM a w]

section Concrete

/-- The joint kernel `P(t,x) = (K_t)_{ij}(x)`. -/
abbrev Pk (i j : Fin 3) : ℝ × Space → ℝ := fun p => IIIa.heatLerayK p.1 i j p.2

/-- `D_k(t,x) = ∂_k (K_t)_{ij}(x)` as a function of `(t,x)`. -/
def DK (i j k : Fin 3) : ℝ × Space → ℝ :=
  fun q => fderiv ℝ (Pk i j) q (0, UnforcedLeray.coordinateVector k)

lemma slice_eq (hC : HeatLerayKJointC3) (i j : Fin 3) {τ : ℝ} (hτ : 0 < τ) (x w : Space) :
    fderiv ℝ (fun x' => IIIa.heatLerayK τ i j x') x w = fderiv ℝ (Pk i j) (τ, x) (0, w) :=
  slice_fderiv (f := Pk i j) (diff0 (hC i j) (mem_U hτ)) w

lemma B_eq_lap (hC : HeatLerayKJointC3) (hH : HeatLerayKHeat) (i j : Fin 3) {τ : ℝ} (hτ : 0 < τ)
    (x : Space) :
    fderiv ℝ (Pk i j) (τ, x) (1, 0) =
      ∑ l : Fin 3, fderiv ℝ (fderiv ℝ (Pk i j)) (τ, x)
        (0, UnforcedLeray.coordinateVector l) (0, UnforcedLeray.coordinateVector l) := by
  have hU : (τ, x) ∈ U := mem_U hτ
  have h1 := (hH τ hτ i j x).deriv
  have h2 := time_deriv (diff0 (hC i j) hU)
  have h3 : fderiv ℝ (Pk i j) (τ, x) (1, 0) = deriv (fun s => IIIa.heatLerayK s i j x) τ := h2.symm
  rw [h3, h1]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h4 : (fun y => fderiv ℝ (fun x' => IIIa.heatLerayK τ i j x') y
      (UnforcedLeray.coordinateVector l)) =
      fun y => (fun q => fderiv ℝ (Pk i j) q (0, UnforcedLeray.coordinateVector l)) (τ, y) := by
    funext y; exact slice_eq hC i j hτ y _
  rw [h4, slice_fderiv (eval_differentiable (diff1 (hC i j) hU) _),
    fderiv_Dl (hC i j) hU]

lemma DK_heat (hC : HeatLerayKJointC3) (hH : HeatLerayKHeat) (i j k : Fin 3) {τ : ℝ} (hτ : 0 < τ)
    (x : Space) :
    fderiv ℝ (DK i j k) (τ, x) (1, 0) =
      ∑ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun y'' => DK i j k (τ, y'')) y
        (UnforcedLeray.coordinateVector l)) x (UnforcedLeray.coordinateVector l) := by
  have hP := hC i j
  have hU : (τ, x) ∈ U := mem_U hτ
  set vk : ℝ × Space := (0, UnforcedLeray.coordinateVector k) with hvk
  set vl : Fin 3 → ℝ × Space := fun l => (0, UnforcedLeray.coordinateVector l) with hvl
  have hM := diff2 hP hU
  -- left side
  have hL : fderiv ℝ (DK i j k) (τ, x) (1, 0) =
      ∑ l : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ (Pk i j))) (τ, x) vk (vl l) (vl l) := by
    have e1 : fderiv ℝ (DK i j k) (τ, x) (1, 0) =
        fderiv ℝ (fderiv ℝ (Pk i j)) (τ, x) (1, 0) vk := fderiv_Dl hP hU vk (1, 0)
    have e2 := symm1 hP hU (1, 0) vk
    have e3 : fderiv ℝ (fderiv ℝ (Pk i j)) (τ, x) vk (1, 0) =
        fderiv ℝ (fun q => fderiv ℝ (Pk i j) q (1, 0)) (τ, x) vk :=
      (fderiv_Dl hP hU (1, 0) vk).symm
    have heq : (fun q => fderiv ℝ (Pk i j) q (1, 0)) =ᶠ[nhds (τ, x)]
        fun q => ∑ l : Fin 3, fderiv ℝ (fderiv ℝ (Pk i j)) q (vl l) (vl l) := by
      filter_upwards [isOpen_U.mem_nhds hU] with q hq
      obtain ⟨t', y'⟩ := q
      exact B_eq_lap hC hH i j hq y'
    have e4 : fderiv ℝ (fun q => ∑ l : Fin 3, fderiv ℝ (fderiv ℝ (Pk i j)) q (vl l) (vl l))
        (τ, x) vk = ∑ l : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ (Pk i j))) (τ, x) vk (vl l) (vl l) := by
      rw [fderiv_fun_sum (fun l _ => eval_differentiable (eval_differentiable hM (vl l)) (vl l))]
      simp only [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun l _ => third_eval hP hU vk (vl l) (vl l)
    rw [e1, e2, e3, heq.fderiv_eq, e4]
  rw [hL]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h5 : (fun y => fderiv ℝ (fun y'' => DK i j k (τ, y'')) y
      (UnforcedLeray.coordinateVector l)) =
      fun y => (fun q => fderiv ℝ (fderiv ℝ (Pk i j)) q (vl l) vk) (τ, y) := by
    funext y
    have hy : (τ, y) ∈ U := mem_U hτ
    have hd : DifferentiableAt ℝ (DK i j k) (τ, y) := eval_differentiable (diff1 hP hy) vk
    rw [slice_fderiv hd]
    exact fderiv_Dl hP hy vk _
  rw [h5, slice_fderiv (eval_differentiable (eval_differentiable hM (vl l)) vk), third_eval hP hU,
    symm2 hP hU, symm3 hP hU]

lemma DK_euler (hC : HeatLerayKJointC3) (hE : HeatLerayKEuler) (i j k : Fin 3) {τ : ℝ}
    (hτ : 0 < τ) (x : Space) :
    fderiv ℝ (DK i j k) (τ, x) (0, x) + 2 * τ * fderiv ℝ (DK i j k) (τ, x) (1, 0) =
      -4 * DK i j k (τ, x) := by
  have hP := hC i j
  have hU : (τ, x) ∈ U := mem_U hτ
  have h := hE τ hτ i j k x
  have hd : DifferentiableAt ℝ (DK i j k) (τ, x) := eval_differentiable (diff1 hP hU) _
  have e1 : (fun x' => fderiv ℝ (fun x'' => IIIa.heatLerayK τ i j x'') x'
      (UnforcedLeray.coordinateVector k)) = fun x' => DK i j k (τ, x') := by
    funext x'; exact slice_eq hC i j hτ x' _
  have e2 : (fun s => fderiv ℝ (fun x' => IIIa.heatLerayK s i j x') x
      (UnforcedLeray.coordinateVector k)) =ᶠ[nhds τ] fun s => DK i j k (s, x) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show τ ∈ Set.Ioi (0 : ℝ) from hτ)] with s hs
    exact slice_eq hC i j hs x _
  rw [e1, e2.deriv_eq, slice_fderiv hd, time_deriv hd, slice_eq hC i j hτ] at h
  exact h

end Concrete

end UnforcedLeray.Short.PartIIIb.Concrete.KerCalc
