import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.B.Tail

/-!
# Heat equation `∂_tK_t = ΔK_t` for the heat-Leray kernel (`HeatLerayKHeat`, source 3598-3610, 3800)

`K_t = δ G_t + ∂_i∂_j ∫_t^∞ G_a da`. Then `∂_tG_t = ΔG_t` (library `Heat.kernel_hasDerivAt_laplacian`),
`∂_t ∂_i∂_j∫_t^∞G = -∂_i∂_jG_t` (`part2_tail_hasDerivAt`) and `Δ∂_i∂_j∫_t^∞G = ∂_i∂_jΔ∫_t^∞G
= -∂_i∂_jG_t` (`lap_tail` and commutation of the partials).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma lap_part2 {T : Space → ℝ} (hT : ContDiff ℝ ∞ T) (i j : Fin 3) (x : Space) :
    Heat.laplacian (IIIa.part2 T i j) x = IIIa.part2 (Heat.laplacian T) i j x := by
  have hg : ∀ l : Fin 3, ContDiff ℝ ∞
      (Dd (UnforcedLeray.coordinateVector l) (Dd (UnforcedLeray.coordinateVector l) T)) :=
    fun l => Dd_smooth (Dd_smooth hT _) _
  have e1 : Heat.laplacian T = fun y => ∑ l : Fin 3,
      Dd (UnforcedLeray.coordinateVector l) (Dd (UnforcedLeray.coordinateVector l) T) y := rfl
  rw [e1, part2_eq_Dd, part2_eq_Dd, Dd_sum _ hg (UnforcedLeray.coordinateVector j),
    Dd_sum _ (fun l => Dd_smooth (hg l) _) (UnforcedLeray.coordinateVector i)]
  change ∑ l : Fin 3, Dd (UnforcedLeray.coordinateVector l) (Dd (UnforcedLeray.coordinateVector l)
      (Dd (UnforcedLeray.coordinateVector i) (Dd (UnforcedLeray.coordinateVector j) T))) x = _
  refine Finset.sum_congr rfl fun l _ => ?_
  set el := UnforcedLeray.coordinateVector l
  set ei := UnforcedLeray.coordinateVector i
  set ej := UnforcedLeray.coordinateVector j
  rw [Dd_comm (Dd_smooth hT ej) el ei, Dd_comm (Dd_smooth (Dd_smooth hT ej) el) el ei,
    Dd_comm hT el ej, Dd_comm (Dd_smooth hT el) el ej]

lemma lap_add {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Space) :
    Heat.laplacian (fun y => f y + g y) x = Heat.laplacian f x + Heat.laplacian g x := by
  have h : ∀ l : Fin 3, Dd (UnforcedLeray.coordinateVector l)
      (Dd (UnforcedLeray.coordinateVector l) (fun y => f y + g y)) x =
      Dd (UnforcedLeray.coordinateVector l) (Dd (UnforcedLeray.coordinateVector l) f) x +
      Dd (UnforcedLeray.coordinateVector l) (Dd (UnforcedLeray.coordinateVector l) g) x := by
    intro l
    rw [Dd_add hf hg, Dd_add (Dd_smooth hf _) (Dd_smooth hg _)]
  change ∑ l : Fin 3, Dd (UnforcedLeray.coordinateVector l)
      (Dd (UnforcedLeray.coordinateVector l) (fun y => f y + g y)) x = _
  rw [Finset.sum_congr rfl (fun l _ => h l), Finset.sum_add_distrib]
  rfl

theorem heatLerayK_heat : UnforcedLeray.Short.PartIIIb.Concrete.HeatLerayKHeat := by
  intro t ht i j x
  have hT := heatTail_smooth ht
  have hP : ContDiff ℝ ∞ (IIIa.part2 (IIIa.heatTail t) i j) :=
    Dd_smooth (Dd_smooth hT _) _
  have hG := heatG_smooth t
  have hLT : Heat.laplacian (IIIa.heatTail t) = fun y => -IIIa.heatG t y :=
    funext fun y => lap_tail ht y
  have hLP : Heat.laplacian (IIIa.part2 (IIIa.heatTail t) i j) x =
      -IIIa.part2 (IIIa.heatG t) i j x := by
    rw [lap_part2 hT, hLT, part2_eq_Dd, part2_eq_Dd, Dd_neg, Dd_neg]
  have hGd : HasDerivAt (fun s => IIIa.heatG s x) (Heat.laplacian (IIIa.heatG t) x) t := by
    have := Heat.kernel_hasDerivAt_laplacian ht x
    simpa only [IIIa.heatG_eq_heatKernel] using this
  have hP' := part2_tail_hasDerivAt ht i j x
  show HasDerivAt (fun s => IIIa.heatLerayK s i j x)
    (Heat.laplacian (fun x' => IIIa.heatLerayK t i j x') x) t
  by_cases hij : i = j
  · have hK : (fun x' => IIIa.heatLerayK t i j x') =
        fun y => IIIa.heatG t y + IIIa.part2 (IIIa.heatTail t) i j y := by
      funext y; simp [IIIa.heatLerayK, hij]
    rw [hK, lap_add hG hP, hLP]
    have hfun : (fun s => IIIa.heatLerayK s i j x) =
        fun s => IIIa.heatG s x + IIIa.part2 (IIIa.heatTail s) i j x := by
      funext s; simp [IIIa.heatLerayK, hij]
    rw [hfun]
    exact (hGd.fun_add hP').congr_deriv (by ring)
  · have hK : (fun x' => IIIa.heatLerayK t i j x') =
        fun y => 0 + IIIa.part2 (IIIa.heatTail t) i j y := by
      funext y; simp [IIIa.heatLerayK, hij]
    rw [hK, lap_add contDiff_const hP, hLP]
    have h0 : Heat.laplacian (fun _ : Space => (0 : ℝ)) x = 0 := by
      simp [Heat.laplacian]
    rw [h0]
    have hfun : (fun s => IIIa.heatLerayK s i j x) =
        fun s => 0 + IIIa.part2 (IIIa.heatTail s) i j x := by
      funext s; simp [IIIa.heatLerayK, hij]
    rw [hfun]
    exact (hP'.const_add 0).congr_deriv (by ring)

end UnforcedLeray.Short.PartIIIb.Concrete
