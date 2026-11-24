import UnforcedLeray.Lib.TrainB.InitialDatumH3
import UnforcedLeray.Lib.Kernels.IterApply

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

private def listDirections (vs : List Plane) : Fin vs.length → Plane := fun i => vs.get i

private theorem norm_cylDir_eq_one (i : Fin 2) : ‖Sob.cylDir i‖ = 1 := by
  fin_cases i <;> simp [Sob.cylDir, Prod.norm_def]

private theorem iterD_eq_iteratedFDeriv_apply (vs : List Plane) (u : Plane → Vec2)
    (hu : ContDiff ℝ ∞ u) :
    Sob.iterD vs u = fun z =>
      iteratedFDeriv ℝ vs.length u z (listDirections vs) := by
  induction vs with
  | nil =>
      funext z
      simp [Sob.iterD, iteratedFDeriv_zero_apply]
  | cons v vs ih =>
      funext z
      change fderiv ℝ (Sob.iterD vs u) z v =
        iteratedFDeriv ℝ (vs.length + 1) u z (listDirections (v :: vs))
      have hm : listDirections (v :: vs) = Fin.cons v (listDirections vs) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      rw [hm, iteratedFDeriv_succ_apply_left]
      simp only [Fin.cons_zero, Fin.tail_cons]
      rw [ih]
      have hD : ContDiff ℝ ∞ (iteratedFDeriv ℝ vs.length u) :=
        hu.iteratedFDeriv_right (m := ∞) (i := vs.length)
          UnforcedLeray.Kernels.infty_add_nat_le
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ vs.length u) z :=
        (contDiff_iff_contDiffAt.mp hD z).differentiableAt (by simp)
      exact fderiv_continuousMultilinear_apply_const_apply hdiff (listDirections vs) v

private theorem isCylSmooth_smul_periodic_test {c : ℝ} {u : Plane → Vec2}
    {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) (hu : ContDiff ℝ ∞ u)
    (hper : IsPeriodic c u) : Sob.IsCylSmooth c (fun z => φ z • u z) := by
  refine ⟨hφ.smooth.smul hu, fun z => ?_, ?_⟩
  · rw [hφ.periodic]
    have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
    rw [hz, hper]
  · obtain ⟨R, hR⟩ := hφ.bounded
    exact ⟨R, fun z hz => by rw [hR z hz, zero_smul]⟩

private theorem periodic_fderiv_initial {c : ℝ} {u : Plane → Vec2}
    (hper : IsPeriodic c u) (v : Plane) :
    IsPeriodic c (fun z => fderiv ℝ u z v) := by
  intro z
  change fderiv ℝ u (z.1 + c, z.2) v = fderiv ℝ u z v
  have e : (fun y : Plane => u (y + (c, 0))) = u := by
    funext y
    have hy : y + (c, 0) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hper y
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := z) ((c, 0) : Plane)
  rw [e] at hd
  have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
  rw [← hz, ← hd]

private theorem iterD_periodic {c : ℝ} {u : Plane → Vec2} (hper : IsPeriodic c u) :
    ∀ vs : List Plane, IsPeriodic c (Sob.iterD vs u)
  | [] => by simpa using hper
  | v :: vs => by
      simpa only [Sob.iterD_cons] using periodic_fderiv_initial (iterD_periodic hper vs) v

/-- Every ordered classical directional derivative of a smooth periodic field is its cylinder
weak derivative, with no compact-axial hypothesis on the field itself. -/
theorem hasWeakDeriv_cylinder_word_of_smooth_periodic {c : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : ContDiff ℝ ∞ u) (hper : IsPeriodic c u) :
    ∀ vs : List Plane,
      Sob.HasWeakDeriv (Sob.cylinder c) vs u (Sob.iterD vs u) := by
  intro vs
  induction vs with
  | nil =>
      refine Sob.HasWeakDeriv.nil fun φ hφ => ?_
      exact (isCylSmooth_smul_periodic_test hφ hu hper).integrableOn
  | cons v vs ih =>
      exact ih.cons (hasWeakDeriv_cylinder_dir_of_smooth_periodic hc
        (Sob.contDiff_iterD hu vs) (iterD_periodic hper vs) v)

/-- Every actual ordered Train derivative of the Gaussian datum is finite in centered-cell L²;
this transfers B0141's Fréchet-jet statement by the norm-one coordinate directional evaluations. -/
theorem memLp_datum_word_derivative {c : ℝ} (hc : 0 < c) (α : Sob.Idx 2 3) :
    MemLp (Sob.iterD ((Sob.cylinder c).word α) (Train.datum c)) 2 (Cyl.cellμ c) := by
  let vs := (Sob.cylinder c).word α
  let k := vs.length
  have hjet : MemLp (Train.jet k (Train.datum c)) 2 (Cyl.cellμ c) :=
    B0141.memHAll_datum hc k
  have hnorm : MemLp (fun z => ‖Train.jet k (Train.datum c) z‖) 2 (Cyl.cellμ c) :=
    hjet.norm
  have hcont : Continuous (Sob.iterD vs (Train.datum c)) :=
    (Sob.contDiff_iterD (Train.datum_contDiff hc.ne') vs).continuous
  apply hnorm.mono' hcont.aestronglyMeasurable
  filter_upwards with z
  rw [iterD_eq_iteratedFDeriv_apply vs (Train.datum c)
    (Train.datum_contDiff hc.ne')]
  have hbound := (iteratedFDeriv ℝ k (Train.datum c) z).le_opNorm (listDirections vs)
  have hprod : ∏ i : Fin k, ‖listDirections vs i‖ = 1 := by
    have hword : ∀ v ∈ vs, ‖v‖ = 1 := by
      intro v hv
      have hv' : v ∈ List.ofFn (fun j : Fin α.1.1 => (Sob.cylinder c).dir (α.2 j)) := by
        simpa [vs, Sob.TestDomain.word] using hv
      rcases (List.mem_ofFn' _ _).mp hv' with ⟨i, hi⟩
      rw [← hi]
      exact norm_cylDir_eq_one (α.2 i)
    have heach (i : Fin k) : ‖listDirections vs i‖ = 1 :=
      hword (vs.get i) (List.get_mem vs i)
    calc
      ∏ i : Fin k, ‖listDirections vs i‖ = ∏ i : Fin k, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact heach i
      _ = 1 := by simp
  calc
    ‖iteratedFDeriv ℝ k (Train.datum c) z (listDirections vs)‖ ≤
        ‖iteratedFDeriv ℝ k (Train.datum c) z‖ *
          ∏ i : Fin k, ‖listDirections vs i‖ := hbound
    _ = ‖Train.jet k (Train.datum c) z‖ := by simp [Train.jet, hprod]

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.hasWeakDeriv_cylinder_word_of_smooth_periodic
#print axioms UnforcedLeray.TrainB.memLp_datum_word_derivative
