import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.U
import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.Fields
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# `GEQFieldCell` from global inlet integrability (Hölder)

Source `the November 2 reference manuscript`
lines 2562-2564 (Hölder: one factor in `L^∞`, the other in `Y_p`), 1478-1480 (periodic field in
`L^{q₀}` represents an element of `Y_{q₀}`).  The factors of `GEQuadField` are: `u ∈ L^∞` (bounded
inlet plus `geSupBound`), `Du ∈ L^{2q₀}` (`GEQHyp`, global inlet derivative), `D²u ∈ L^{q₀}`
(global inlet Hessian plus the `Yq` Hessian `rep (h j k)`).  Periodicity in `τ` comes from
`rep_add_period` and the `P`-periodicity of the inlet (`inletProfile_periodic`, `period_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.Axi
open UnforcedLeray.Cons.C03.Concrete (Params rep rep_add_period stronglyMeasurable_rep)

/-- The phase cell measure `(0,P] × ℝ³`. -/
abbrev cellMeasure (P : ℝ) : Measure (ℝ × UnforcedLeray.Space) :=
  (volume.restrict (Ioc (0 : ℝ) P)).prod volume

theorem memLp_coord' {X : Type*} [MeasurableSpace X] {μ : Measure X} {r : ℝ≥0∞}
    {f : X → UnforcedLeray.PhaseSpace.CVec3} (hf : MemLp f r μ) (i : Fin 3) :
    MemLp (fun x => f x i) r μ :=
  (EuclideanSpace.proj i : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).comp_memLp' hf

theorem measurable_coord' {X : Type*} [MeasurableSpace X]
    {f : X → UnforcedLeray.PhaseSpace.CVec3} (hf : Measurable f) (i : Fin 3) :
    Measurable (fun x => f x i) :=
  ((EuclideanSpace.proj i : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.measurable).comp hf

theorem dy_contDiff' {f : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    (hf : ContDiff ℝ ∞ f) (j : Fin 3) : ContDiff ℝ ∞ (UnforcedLeray.PhaseSpace.dy j f) := by
  unfold UnforcedLeray.PhaseSpace.dy
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem dy_periodic' {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    (hper : ∀ x, Φ (x.1 + P, x.2) = Φ x) (j : Fin 3) (x : ℝ × UnforcedLeray.Space) :
    UnforcedLeray.PhaseSpace.dy j Φ (x.1 + P, x.2) = UnforcedLeray.PhaseSpace.dy j Φ x := by
  have hx : ((x.1 + P, x.2) : ℝ × UnforcedLeray.Space) =
      x + ((P : ℝ), (0 : UnforcedLeray.Space)) := by
    ext <;> simp
  have key : ∀ y : ℝ × UnforcedLeray.Space,
      Φ (y + ((P : ℝ), (0 : UnforcedLeray.Space))) = Φ y := by
    intro y
    have hy : y + ((P : ℝ), (0 : UnforcedLeray.Space)) = (y.1 + P, y.2) := by
      ext <;> simp
    rw [hy]
    exact hper y
  have hf : fderiv ℝ Φ (x + ((P : ℝ), (0 : UnforcedLeray.Space))) = fderiv ℝ Φ x := by
    rw [← fderiv_comp_add_right]
    congr 1
    funext y
    exact key y
  unfold UnforcedLeray.PhaseSpace.dy
  rw [hx, hf]

theorem inlet_period' (p : Params) (i : Fin 2) (τ : ℝ) (y : UnforcedLeray.Space) :
    p.inlet i (τ + p.period) y = p.inlet i τ y := by
  have hR : p.R ≠ 0 := p.R_pos.ne'
  have hRP : p.R * p.period / 2 = p.c := by
    rw [p.period_eq]
    field_simp
  have hph : UnforcedLeray.Axi.phase p.R (τ + p.period) y =
      UnforcedLeray.Axi.phase p.R τ y + p.c := by
    unfold UnforcedLeray.Axi.phase
    linear_combination hRP
  have hch : UnforcedLeray.Axi.chart p.R (τ + p.period) y =
      (UnforcedLeray.Axi.age p.R y,
        (UnforcedLeray.Axi.phase p.R τ y + p.c, UnforcedLeray.Axi.trans p.R y)) := by
    unfold UnforcedLeray.Axi.chart
    rw [hph]
  have hinv : p.inletProfile i
      (UnforcedLeray.Axi.age p.R y,
        (UnforcedLeray.Axi.phase p.R τ y + p.c, UnforcedLeray.Axi.trans p.R y)) =
      p.inletProfile i (UnforcedLeray.Axi.chart p.R τ y) :=
    p.inletProfile_periodic i _ _ _
  unfold Params.inlet UnforcedLeray.Axi.Nv
  rw [hch, hinv]

theorem eFun_period' (p : Params) (α : Fin 2 → ℝ) (x : ℝ × UnforcedLeray.Space) :
    p.eFun α (x.1 + p.period, x.2) = p.eFun α x := by
  simp only [Params.eFun, inlet_period']

theorem gEQFieldCell_of_inlet : GEQInletGlobal → GEQFieldCell := by
  intro hInl lam q hq dm dp hdm
  obtain ⟨n1, hn1, H1⟩ := hInl lam q hq dm dp hdm
  obtain ⟨n2, hn2, H2⟩ := geSupBound lam q hq dm dp hdm
  refine ⟨min 1 (min n1 n2), lt_min one_pos (lt_min hn1 hn2), ?_⟩
  intro p d hreg hν hmode z g hd
  intro h hh j
  haveI : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_left _ _)
  have hνn1 : p.ν ≤ n1 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνn2 : p.ν ≤ n2 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have HI := H1 p d hreg hνn1 hmode z g hd
  obtain ⟨M, -, hM⟩ := H2 p d hreg hνn2 hmode z g hd
  obtain ⟨Ce, hCe⟩ := (HI 0 0).2.2
  -- smoothness of the inlet
  have heC : ContDiff ℝ ∞ (p.eFun (p.coord z)) := by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν1 hmode l).const_smul _
  -- periodicity
  have hper_e : ∀ x : ℝ × UnforcedLeray.Space,
      p.eFun (p.coord z) (x.1 + p.period, x.2) = p.eFun (p.coord z) x :=
    fun x => eFun_period' p (p.coord z) x
  have hper_de : ∀ k : Fin 3, ∀ x : ℝ × UnforcedLeray.Space,
      UnforcedLeray.PhaseSpace.dy k (p.eFun (p.coord z)) (x.1 + p.period, x.2) =
        UnforcedLeray.PhaseSpace.dy k (p.eFun (p.coord z)) x :=
    fun k x => dy_periodic' hper_e k x
  have hper_dde : ∀ j k : Fin 3, ∀ x : ℝ × UnforcedLeray.Space,
      UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy k (p.eFun (p.coord z)))
          (x.1 + p.period, x.2) =
        UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy k (p.eFun (p.coord z))) x :=
    fun j k x => dy_periodic' (fun y => hper_de k y) j x
  have hU' : ∀ x : ℝ × UnforcedLeray.Space,
      p.uOf z (x.1 + p.period, x.2) = p.uOf z x := by
    intro x
    show p.eFun (p.coord z) (x.1 + p.period, x.2) + rep (p.wOf z) (x.1 + p.period) x.2 =
      p.eFun (p.coord z) x + rep (p.wOf z) x.1 x.2
    rw [hper_e x, rep_add_period]
  have hG1 : ∀ (k : Fin 3) (x : ℝ × UnforcedLeray.Space),
      GEQDu p z g k (x.1 + p.period, x.2) = GEQDu p z g k x := by
    intro k x
    show UnforcedLeray.PhaseSpace.dy k (p.eFun (p.coord z)) (x.1 + p.period, x.2) +
        rep (g k) (x.1 + p.period) x.2 =
      UnforcedLeray.PhaseSpace.dy k (p.eFun (p.coord z)) x + rep (g k) x.1 x.2
    rw [hper_de k x, rep_add_period]
  have hDDu' : ∀ (j k : Fin 3) (x : ℝ × UnforcedLeray.Space),
      GEQDdu p z g h j k (x.1 + p.period, x.2) = GEQDdu p z g h j k x := by
    intro j k x
    show UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy k (p.eFun (p.coord z)))
        (x.1 + p.period, x.2) + rep (h j k) (x.1 + p.period) x.2 =
      UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy k (p.eFun (p.coord z))) x +
        rep (h j k) x.1 x.2
    rw [hper_dde j k x, rep_add_period]
  have hperF : ∀ x : ℝ × UnforcedLeray.Space,
      GEQuadField p z g h j (x.1 + p.period, x.2) = GEQuadField p z g h j x := by
    intro x
    simp only [GEQuadField, hU', hG1, hDDu']
  -- strong measurability of the pieces
  have hsU : StronglyMeasurable (fun x : ℝ × UnforcedLeray.Space => p.uOf z x) :=
    heC.continuous.stronglyMeasurable.add (stronglyMeasurable_rep (p.wOf z))
  have hsDu : ∀ k : Fin 3, StronglyMeasurable (GEQDu p z g k) := fun k =>
    (dy_contDiff' heC k).continuous.stronglyMeasurable.add (stronglyMeasurable_rep (g k))
  have hsDDu : ∀ j k : Fin 3, StronglyMeasurable (GEQDdu p z g h j k) := fun j k =>
    (dy_contDiff' (dy_contDiff' heC k) j).continuous.stronglyMeasurable.add
      (stronglyMeasurable_rep (h j k))
  have hGQ : ∀ (i : Fin 3) (x : ℝ × UnforcedLeray.Space), GEQuadField p z g h j x i =
      -∑ k : Fin 3, (GEQDdu p z g h k j x k * p.uOf z x i + GEQDu p z g k x k * GEQDu p z g j x i +
        GEQDu p z g j x k * GEQDu p z g k x i + p.uOf z x k * GEQDdu p z g h k j x i) :=
    fun i x => rfl
  have hmcomp : ∀ i : Fin 3, Measurable (fun x => GEQuadField p z g h j x i) := by
    intro i
    have e1 : (fun x => GEQuadField p z g h j x i) = fun x =>
        -∑ k : Fin 3, (GEQDdu p z g h k j x k * p.uOf z x i + GEQDu p z g k x k * GEQDu p z g j x i +
          GEQDu p z g j x k * GEQDu p z g k x i + p.uOf z x k * GEQDdu p z g h k j x i) :=
      funext fun x => hGQ i x
    rw [e1]
    refine Measurable.neg (Finset.measurable_sum _ fun k _ => ?_)
    have m1 := measurable_coord' (hsDDu k j).measurable k
    have m2 := measurable_coord' hsU.measurable i
    have m3 := measurable_coord' (hsDu k).measurable k
    have m4 := measurable_coord' (hsDu j).measurable i
    have m5 := measurable_coord' (hsDu j).measurable k
    have m6 := measurable_coord' (hsDu k).measurable i
    have m7 := measurable_coord' hsU.measurable k
    have m8 := measurable_coord' (hsDDu k j).measurable i
    exact (((m1.mul m2).add (m3.mul m4)).add (m5.mul m6)).add (m7.mul m8)
  have hSMpi : StronglyMeasurable (fun x => (fun i : Fin 3 => GEQuadField p z g h j x i)) :=
    (measurable_pi_lambda _ hmcomp).stronglyMeasurable
  have hSM : StronglyMeasurable (GEQuadField p z g h j) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp_stronglyMeasurable hSMpi
  -- Lebesgue bounds
  have hrepL : ∀ w : Yq p.period UnforcedLeray.B0412.q0E,
      MemLp (fun x : ℝ × UnforcedLeray.Space => rep w x.1 x.2) UnforcedLeray.B0412.q0E
        (cellMeasure p.period) := by
    intro w
    have hm : (volume : Measure (ℝ × UnforcedLeray.Space)).restrict
        (Ioc (0 : ℝ) p.period ×ˢ (univ : Set UnforcedLeray.Space)) =
        cellMeasure p.period := by
      simpa only [cellMeasure, Measure.volume_eq_prod] using
        (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
          (ν := (volume : Measure UnforcedLeray.Space)) (Ioc (0 : ℝ) p.period)).symm
    have hL := UnforcedLeray.Cons.C03.Concrete.memLp_rep_periodCell (P := p.period)
      (q := UnforcedLeray.B0412.q0E) UnforcedLeray.B0412.q0E_ne_top w
    rw [hm] at hL
    exact hL
  have hMemDu : ∀ k : Fin 3, MemLp (GEQDu p z g k) (2 * UnforcedLeray.B0412.q0E)
      (cellMeasure p.period) := fun k => (HI k 0).1.add (hh.2 k)
  have hDDu : ∀ j k : Fin 3, MemLp (GEQDdu p z g h j k) UnforcedLeray.B0412.q0E
      (cellMeasure p.period) := fun j k => (HI j k).2.1.add (hrepL (h j k))
  have hMc : ∀ᵐ x ∂(cellMeasure p.period), ‖rep (p.wOf z) x.1 x.2‖ ≤ M := hM
  have hUb : ∀ᵐ x ∂(cellMeasure p.period), ‖p.uOf z x‖ ≤ Ce + M := by
    filter_upwards [hMc] with x hx
    show ‖p.eFun (p.coord z) x + rep (p.wOf z) x.1 x.2‖ ≤ Ce + M
    exact (norm_add_le _ _).trans (add_le_add (hCe x) hx)
  have hUinf : MemLp (fun x : ℝ × UnforcedLeray.Space => p.uOf z x) ∞ (cellMeasure p.period) :=
    memLp_top_of_bound hsU.aestronglyMeasurable (Ce + M) hUb
  haveI hH2 : ENNReal.HolderTriple (2 * UnforcedLeray.B0412.q0E) (2 * UnforcedLeray.B0412.q0E)
      UnforcedLeray.B0412.q0E := by
    refine (ENNReal.holderTriple_iff _ _ _).2 ?_
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul]
  have T1 : ∀ k i : Fin 3, MemLp (fun x => GEQDdu p z g h k j x k * p.uOf z x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun k i => MemLp.mul (memLp_coord' hUinf i) (memLp_coord' (hDDu k j) k)
  have T2 : ∀ k i : Fin 3, MemLp (fun x => GEQDu p z g k x k * GEQDu p z g j x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun k i => MemLp.mul (memLp_coord' (hMemDu j) i) (memLp_coord' (hMemDu k) k)
  have T3 : ∀ k i : Fin 3, MemLp (fun x => GEQDu p z g j x k * GEQDu p z g k x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun k i => MemLp.mul (memLp_coord' (hMemDu k) i) (memLp_coord' (hMemDu j) k)
  have T4 : ∀ k i : Fin 3, MemLp (fun x => p.uOf z x k * GEQDdu p z g h k j x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun k i => MemLp.mul (memLp_coord' (hDDu k j) i) (memLp_coord' hUinf k)
  have hcomp : ∀ i : Fin 3, MemLp (fun x => GEQuadField p z g h j x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) := by
    intro i
    have hk : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
        MemLp (fun x => GEQDdu p z g h k j x k * p.uOf z x i + GEQDu p z g k x k * GEQDu p z g j x i +
          GEQDu p z g j x k * GEQDu p z g k x i + p.uOf z x k * GEQDdu p z g h k j x i)
          UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
      fun k _ => (((T1 k i).add (T2 k i)).add (T3 k i)).add (T4 k i)
    have hs := memLp_finsetSum Finset.univ hk
    have hfun : (fun x => GEQuadField p z g h j x i) = fun x =>
        -∑ k ∈ Finset.univ, (GEQDdu p z g h k j x k * p.uOf z x i + GEQDu p z g k x k * GEQDu p z g j x i +
          GEQDu p z g j x k * GEQDu p z g k x i + p.uOf z x k * GEQDdu p z g h k j x i) :=
      funext fun x => hGQ i x
    rw [hfun]
    exact hs.neg
  have hL : MemLp (GEQuadField p z g h j) UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    MeasureTheory.memLp_piLp_iff.2 hcomp
  have hq0 : UnforcedLeray.B0412.q0E ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ UnforcedLeray.B0412.q0E))
  have hfin : ∫⁻ τ in Ioc (0 : ℝ) p.period, ∫⁻ y, ‖GEQuadField p z g h j (τ, y)‖ₑ ^
      UnforcedLeray.B0412.q0E.toReal < ⊤ := by
    have h1 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0
      UnforcedLeray.B0412.q0E_ne_top).1 hL.eLpNorm_lt_top
    have hae : AEMeasurable (fun x => ‖GEQuadField p z g h j x‖ₑ ^
        UnforcedLeray.B0412.q0E.toReal) (cellMeasure p.period) :=
      (hL.aestronglyMeasurable.enorm).pow_const _
    have h2 : ∫⁻ x, ‖GEQuadField p z g h j x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal
        ∂(cellMeasure p.period) = ∫⁻ τ in Ioc (0 : ℝ) p.period, ∫⁻ y,
          ‖GEQuadField p z g h j (τ, y)‖ₑ ^ UnforcedLeray.B0412.q0E.toReal :=
      lintegral_prod _ hae
    rw [h2] at h1
    exact h1
  refine ⟨hSM, ?_, hfin⟩
  exact ae_of_all _ fun τ => ae_of_all _ fun y => hperF (τ, y)

end UnforcedLeray.Short.PartIIIb.Concrete
