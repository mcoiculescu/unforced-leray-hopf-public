import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- Swapping the first two directions of an iterated derivative of a smooth field
(Schwarz symmetry of the second derivative of `iterD L u`). -/
theorem iterD_swap_head {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : Plane → F} (hu : ContDiff ℝ ∞ u) (v w : Plane) (L : List Plane) :
    Sob.iterD (v :: w :: L) u = Sob.iterD (w :: v :: L) u := by
  have hG : ContDiff ℝ ∞ (Sob.iterD L u) := Sob.contDiff_iterD hu L
  have h1 : ∀ (a b x : Plane), fderiv ℝ (fun y => fderiv ℝ (Sob.iterD L u) y a) x b
      = fderiv ℝ (fderiv ℝ (Sob.iterD L u)) x b a := by
    intro a b x
    have hdf : DifferentiableAt ℝ (fderiv ℝ (Sob.iterD L u)) x :=
      (hG.fderiv_right (m := 1) (by simp)).differentiable (by simp) x
    have hc := fderiv_clm_apply (c := fderiv ℝ (Sob.iterD L u)) (u := fun _ => a) hdf
      (differentiableAt_const a)
    have := congrArg (fun L => L b) hc
    simpa [fderiv_const] using this
  funext x
  have hsymm := hG.contDiffAt.isSymmSndFDerivAt (x := x) (by simp)
  simp only [Sob.iterD_cons]
  rw [h1, h1]
  exact hsymm v w

/-- Permuting the direction list of an iterated derivative of a smooth field does not change it. -/
theorem iterD_perm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : Plane → F} (hu : ContDiff ℝ ∞ u) {L1 L2 : List Plane} (h : L1.Perm L2) :
    Sob.iterD L1 u = Sob.iterD L2 u := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [Sob.iterD_cons, Sob.iterD_cons, ih]
  | swap x y l => exact iterD_swap_head hu y x l
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Concatenation of direction lists composes the iterated derivatives. -/
theorem iterD_append_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Plane → F) (L1 L2 : List Plane) :
    Sob.iterD (L1 ++ L2) u = Sob.iterD L1 (Sob.iterD L2 u) := by
  induction L1 with
  | nil => rfl
  | cons a L ih => simp only [List.cons_append, Sob.iterD_cons, ih]

/-- Iterated derivatives are additive. -/
theorem iterD_add_fun {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u v : Plane → F} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (L : List Plane) :
    Sob.iterD L (fun x => u x + v x) = fun x => Sob.iterD L u x + Sob.iterD L v x := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    funext x
    simp only [Sob.iterD_cons]
    rw [ih]
    have h1 := (Sob.contDiff_iterD hu L).differentiable (by simp) x
    have h2 := (Sob.contDiff_iterD hv L).differentiable (by simp) x
    rw [show (fun x => Sob.iterD L u x + Sob.iterD L v x) = Sob.iterD L u + Sob.iterD L v from rfl,
      fderiv_add h1 h2]
    rfl

/-- Sums of cylinder-smooth fields are cylinder-smooth. -/
theorem isCylSmooth_add_local {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {c : ℝ}
    {u v : ℝ × ℝ → F} (hu : Sob.IsCylSmooth c u) (hv : Sob.IsCylSmooth c v) :
    Sob.IsCylSmooth c (fun x => u x + v x) := by
  refine ⟨hu.smooth.add hv.smooth, fun z => by simp [hu.periodic z, hv.periodic z], ?_⟩
  obtain ⟨R1, h1⟩ := hu.bounded
  obtain ⟨R2, h2⟩ := hv.bounded
  refine ⟨max R1 R2, fun z hz => ?_⟩
  rw [h1 z (lt_of_le_of_lt (le_max_left _ _) hz), h2 z (lt_of_le_of_lt (le_max_right _ _) hz)]
  simp

/-- Equality of elements of the periodic scale `Cyl.H` from equality of all weak derivatives. -/
theorem cylH_ext {c : ℝ} {k : ℕ} {x y : Cyl.H ℝ Cyl.Vec2 c 0 k}
    (h : ∀ α : Sob.Idx 2 k,
      Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 k 2 α x =
      Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 k 2 α y) : x = y := by
  apply Subtype.ext
  apply (WithLp.ext_iff (p := 2)).mpr
  funext α
  exact h α

/-- **Leaf D2** (the Laplacian of a smooth field is the smooth field of the pointwise Laplacian;
source lines 261-288). -/
theorem heatLapSmoothIdentify5 : HeatLapSmoothIdentify5 := by
  intro c hc T hT
  have hA := Sob.IsCylSmooth.iterD hT [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))]
  have hB := Sob.IsCylSmooth.iterD hT [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))]
  have hΔ := isCylSmooth_add_local hA hB
  refine ⟨hΔ, ?_⟩
  unfold smoothH5Field
  apply cylH_ext
  intro α
  have hd0 : (Sob.cylinder c).dir 0 = ((1:ℝ), (0:ℝ)) := rfl
  have hd1 : (Sob.cylinder c).dir 1 = ((0:ℝ), (1:ℝ)) := rfl
  have hw0 : (Sob.cylinder c).word (Sob.Idx.cons (0 : Fin 2) (Sob.Idx.cons (0 : Fin 2) α)) =
      ((1:ℝ), (0:ℝ)) :: ((1:ℝ), (0:ℝ)) :: (Sob.cylinder c).word α := by
    rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_cons, hd0]
  have hw1 : (Sob.cylinder c).word (Sob.Idx.cons (1 : Fin 2) (Sob.Idx.cons (1 : Fin 2) α)) =
      ((0:ℝ), (1:ℝ)) :: ((0:ℝ), (1:ℝ)) :: (Sob.cylinder c).word α := by
    rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_cons, hd1]
  have hdom : ∀ W : List Plane,
      Sob.iterD W (fun x => Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] T x
        + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] T x)
      = fun x => Sob.iterD (((1:ℝ), (0:ℝ)) :: ((1:ℝ), (0:ℝ)) :: W) T x
        + Sob.iterD (((0:ℝ), (1:ℝ)) :: ((0:ℝ), (1:ℝ)) :: W) T x := by
    intro W
    rw [iterD_add_fun hA.smooth hB.smooth W]
    have k0 : Sob.iterD W (Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] T)
        = Sob.iterD (((1:ℝ), (0:ℝ)) :: ((1:ℝ), (0:ℝ)) :: W) T := by
      rw [← iterD_append_eq]
      exact iterD_perm hT.smooth List.perm_append_comm
    have k1 : Sob.iterD W (Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] T)
        = Sob.iterD (((0:ℝ), (1:ℝ)) :: ((0:ℝ), (1:ℝ)) :: W) T := by
      rw [← iterD_append_eq]
      exact iterD_perm hT.smooth List.perm_append_comm
    rw [k0, k1]
  have e0 := Sob.W.deriv_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 5) (p := 2)
    hc T hT (Sob.Idx.cons (0 : Fin 2) (Sob.Idx.cons (0 : Fin 2) α))
  have e1 := Sob.W.deriv_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 5) (p := 2)
    hc T hT (Sob.Idx.cons (1 : Fin 2) (Sob.Idx.cons (1 : Fin 2) α))
  have eR := Sob.W.deriv_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3) (p := 2)
    hc _ hΔ α
  have hLapApp : ∀ x : Cyl.H ℝ Cyl.Vec2 c 0 5, hLap c 3 x =
      Sob.W.partialDeriv (k := 3) 0 (Sob.W.partialDeriv (k := 4) 0 x)
        + Sob.W.partialDeriv (k := 3) 1 (Sob.W.partialDeriv (k := 4) 1 x) := by
    intro x
    rw [hLap, sum_apply, Fin.sum_univ_two]
    rfl
  rw [hLapApp]
  simp only [map_add, Sob.W.deriv_partialDeriv]
  refine MeasureTheory.Lp.ext ((MeasureTheory.Lp.coeFn_add _ _).trans ?_)
  filter_upwards [e0, e1, eR] with x h1 h2 h3
  rw [Pi.add_apply, h1, h2, h3, hw0, hw1, hdom]

end UnforcedLeray.Short.PartI
