import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2.Ibp2Step
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2.InletD3Global
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_6.Holder
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_6.Inlet

/-!
# `gEQYq2 : GEQYq2` (`PartIII-b:C/ward/12/3/2/2/4`)

Source `the November 2 reference manuscript`,
lines 2552-2559, 1515-1531, 2381-2387, 1478-1480.

Each product in `GEQuadField2 p z g k t j l` pairs an order-`≤ 1` factor (`p.uOf z` or
`GEQDu p z g a`, both in `L^∞` on the period cell by `geSupBound`, `gEQInletGlobal`,
`gEQInletD3Global`, and `graphSupEmbedding` applied to `g_a ∈ D_{q₀}`) with an order-`2` or
order-`3` factor (`GEQDdu p z g k a b` or `GEQD3u p z t a b c`, both in `L^{q₀}` on the period
cell by `gEQInletGlobal`, `gEQInletD3Global`, and `memLp_rep_periodCell`).  Hence `GEQuadField2`
is periodic and has finite `L^{q₀}` norm on `(0, P] × ℝ³`, and `periodicFieldToYq_proof` gives
its representative in `Y_{q₀}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.Axi
open UnforcedLeray.Cons.C03.Concrete (Params rep rep_add_period stronglyMeasurable_rep pairF phaseInt)

/-- **Order-2 quadratic field in `Y_{q₀}`** (source 2552-2559, 1515-1531, 2381-2387). -/
theorem gEQYq2 : GEQYq2 := by
  intro lam q hq dm dp hdm
  obtain ⟨n1, hn1, H1⟩ := gEQInletGlobal lam q hq dm dp hdm
  obtain ⟨n2, hn2, H2⟩ := geSupBound lam q hq dm dp hdm
  obtain ⟨n3, hn3, H3⟩ := gEQInletD3Global lam q hq dm dp hdm
  have hn4 : 0 < dm ^ 3 / 12 := by positivity
  refine ⟨min (min 1 (dm ^ 3 / 12)) (min n1 (min n2 n3)),
    lt_min (lt_min one_pos hn4) (lt_min hn1 (lt_min hn2 hn3)), ?_⟩
  intro p d hreg hν hmode z g hd k t hyp j l
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν4 : p.ν ≤ dm ^ 3 / 12 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg hν4
  have hνn1 : p.ν ≤ n1 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνn2 : p.ν ≤ n2 :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hνn3 : p.ν ≤ n3 :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have HI := H1 p d hreg hνn1 hmode z g hd
  obtain ⟨M, -, hM⟩ := H2 p d hreg hνn2 hmode z g hd
  have HD3 := H3 p d hreg hνn3 hmode z g hd
  obtain ⟨Ce, hCe⟩ := (HI 0 0).2.2
  -- smoothness of the inlet
  have heC : ContDiff ℝ ∞ (p.eFun (p.coord z)) := by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun i _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν1 hmode i).const_smul _
  -- periodicity
  have hper_e : ∀ x : ℝ × UnforcedLeray.Space,
      p.eFun (p.coord z) (x.1 + p.period, x.2) = p.eFun (p.coord z) x :=
    fun x => eFun_period' p (p.coord z) x
  have hper_de : ∀ a : Fin 3, ∀ x : ℝ × UnforcedLeray.Space,
      dy a (p.eFun (p.coord z)) (x.1 + p.period, x.2) = dy a (p.eFun (p.coord z)) x :=
    fun a x => dy_periodic' hper_e a x
  have hper_dde : ∀ a b : Fin 3, ∀ x : ℝ × UnforcedLeray.Space,
      dy a (dy b (p.eFun (p.coord z))) (x.1 + p.period, x.2) =
        dy a (dy b (p.eFun (p.coord z))) x :=
    fun a b x => dy_periodic' (fun y => hper_de b y) a x
  have hper_d3e : ∀ a b c : Fin 3, ∀ x : ℝ × UnforcedLeray.Space,
      dy c (dy b (dy a (p.eFun (p.coord z)))) (x.1 + p.period, x.2) =
        dy c (dy b (dy a (p.eFun (p.coord z)))) x :=
    fun a b c x => dy_periodic' (fun y => hper_dde b a y) c x
  have hU' : ∀ x : ℝ × UnforcedLeray.Space,
      p.uOf z (x.1 + p.period, x.2) = p.uOf z x := by
    intro x
    show p.eFun (p.coord z) (x.1 + p.period, x.2) + rep (p.wOf z) (x.1 + p.period) x.2 =
      p.eFun (p.coord z) x + rep (p.wOf z) x.1 x.2
    rw [hper_e x, rep_add_period]
  have hG1 : ∀ (a : Fin 3) (x : ℝ × UnforcedLeray.Space),
      GEQDu p z g a (x.1 + p.period, x.2) = GEQDu p z g a x := by
    intro a x
    show dy a (p.eFun (p.coord z)) (x.1 + p.period, x.2) + rep (g a) (x.1 + p.period) x.2 =
      dy a (p.eFun (p.coord z)) x + rep (g a) x.1 x.2
    rw [hper_de a x, rep_add_period]
  have hDDu' : ∀ (a b : Fin 3) (x : ℝ × UnforcedLeray.Space),
      GEQDdu p z g k a b (x.1 + p.period, x.2) = GEQDdu p z g k a b x := by
    intro a b x
    show dy a (dy b (p.eFun (p.coord z))) (x.1 + p.period, x.2) +
        rep (k a b) (x.1 + p.period) x.2 =
      dy a (dy b (p.eFun (p.coord z))) x + rep (k a b) x.1 x.2
    rw [hper_dde a b x, rep_add_period]
  have hD3u' : ∀ (a b c : Fin 3) (x : ℝ × UnforcedLeray.Space),
      GEQD3u p z t a b c (x.1 + p.period, x.2) = GEQD3u p z t a b c x := by
    intro a b c x
    show dy c (dy b (dy a (p.eFun (p.coord z)))) (x.1 + p.period, x.2) +
        rep (t a b c) (x.1 + p.period) x.2 =
      dy c (dy b (dy a (p.eFun (p.coord z)))) x + rep (t a b c) x.1 x.2
    rw [hper_d3e a b c x, rep_add_period]
  have hperF : ∀ x : ℝ × UnforcedLeray.Space,
      GEQuadField2 p z g k t j l (x.1 + p.period, x.2) = GEQuadField2 p z g k t j l x := by
    intro x
    simp only [GEQuadField2, hU', hG1, hDDu', hD3u']
  -- strong measurability of the pieces
  have hsU : StronglyMeasurable (fun x : ℝ × UnforcedLeray.Space => p.uOf z x) :=
    heC.continuous.stronglyMeasurable.add (stronglyMeasurable_rep (p.wOf z))
  have hsDu : ∀ a : Fin 3, StronglyMeasurable (GEQDu p z g a) := fun a =>
    (dy_contDiff' heC a).continuous.stronglyMeasurable.add (stronglyMeasurable_rep (g a))
  have hsDDu : ∀ a b : Fin 3, StronglyMeasurable (GEQDdu p z g k a b) := fun a b =>
    (dy_contDiff' (dy_contDiff' heC b) a).continuous.stronglyMeasurable.add
      (stronglyMeasurable_rep (k a b))
  have hsD3u : ∀ a b c : Fin 3, StronglyMeasurable (GEQD3u p z t a b c) := fun a b c =>
    (dy_contDiff' (dy_contDiff' (dy_contDiff' heC a) b) c).continuous.stronglyMeasurable.add
      (stronglyMeasurable_rep (t a b c))
  have hGQ2 : ∀ (i : Fin 3) (x : ℝ × UnforcedLeray.Space), GEQuadField2 p z g k t j l x i =
      ∑ m : Fin 3,
        (GEQD3u p z t m l j x m * p.uOf z x i + GEQDdu p z g k m l x m * GEQDu p z g j x i +
          GEQDdu p z g k m j x m * GEQDu p z g l x i + GEQDu p z g m x m * GEQDdu p z g k l j x i +
          GEQDdu p z g k l j x m * GEQDu p z g m x i + GEQDu p z g l x m * GEQDdu p z g k m j x i +
          GEQDu p z g j x m * GEQDdu p z g k m l x i + p.uOf z x m * GEQD3u p z t m l j x i) :=
    fun i x => rfl
  have hmcomp : ∀ i : Fin 3, Measurable (fun x => GEQuadField2 p z g k t j l x i) := by
    intro i
    have e1 : (fun x => GEQuadField2 p z g k t j l x i) = fun x =>
        ∑ m : Fin 3,
          (GEQD3u p z t m l j x m * p.uOf z x i + GEQDdu p z g k m l x m * GEQDu p z g j x i +
            GEQDdu p z g k m j x m * GEQDu p z g l x i + GEQDu p z g m x m * GEQDdu p z g k l j x i +
            GEQDdu p z g k l j x m * GEQDu p z g m x i + GEQDu p z g l x m * GEQDdu p z g k m j x i +
            GEQDu p z g j x m * GEQDdu p z g k m l x i + p.uOf z x m * GEQD3u p z t m l j x i) :=
      funext fun x => hGQ2 i x
    rw [e1]
    refine Finset.measurable_sum _ fun m _ => ?_
    have m1 := (measurable_coord' (hsD3u m l j).measurable m).mul (measurable_coord' hsU.measurable i)
    have m2 := (measurable_coord' (hsDDu m l).measurable m).mul (measurable_coord' (hsDu j).measurable i)
    have m3 := (measurable_coord' (hsDDu m j).measurable m).mul (measurable_coord' (hsDu l).measurable i)
    have m4 := (measurable_coord' (hsDu m).measurable m).mul (measurable_coord' (hsDDu l j).measurable i)
    have m5 := (measurable_coord' (hsDDu l j).measurable m).mul (measurable_coord' (hsDu m).measurable i)
    have m6 := (measurable_coord' (hsDu l).measurable m).mul (measurable_coord' (hsDDu m j).measurable i)
    have m7 := (measurable_coord' (hsDu j).measurable m).mul (measurable_coord' (hsDDu m l).measurable i)
    have m8 := (measurable_coord' hsU.measurable m).mul (measurable_coord' (hsD3u m l j).measurable i)
    exact ((((((m1.add m2).add m3).add m4).add m5).add m6).add m7).add m8
  have hSMpi : StronglyMeasurable (fun x => (fun i : Fin 3 => GEQuadField2 p z g k t j l x i)) :=
    (measurable_pi_lambda _ hmcomp).stronglyMeasurable
  have hSM : StronglyMeasurable (GEQuadField2 p z g k t j l) :=
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
  have hDDu : ∀ a b : Fin 3, MemLp (GEQDdu p z g k a b) UnforcedLeray.B0412.q0E
      (cellMeasure p.period) := fun a b => (HI a b).2.1.add (hrepL (k a b))
  have hD3u : ∀ a b c : Fin 3, MemLp (GEQD3u p z t a b c) UnforcedLeray.B0412.q0E
      (cellMeasure p.period) := fun a b c => (HD3 a b c).1.add (hrepL (t a b c))
  have hMc : ∀ᵐ x ∂(cellMeasure p.period), ‖rep (p.wOf z) x.1 x.2‖ ≤ M := hM
  have hUb : ∀ᵐ x ∂(cellMeasure p.period), ‖p.uOf z x‖ ≤ Ce + M := by
    filter_upwards [hMc] with x hx
    show ‖p.eFun (p.coord z) x + rep (p.wOf z) x.1 x.2‖ ≤ Ce + M
    exact (norm_add_le _ _).trans (add_le_add (hCe x) hx)
  have hUinf : MemLp (fun x : ℝ × UnforcedLeray.Space => p.uOf z x) ∞ (cellMeasure p.period) :=
    memLp_top_of_bound hsU.aestronglyMeasurable (Ce + M) hUb
  have hDuInf : ∀ a : Fin 3, MemLp (GEQDu p z g a) ∞ (cellMeasure p.period) := by
    intro a
    obtain ⟨Cde, hCde⟩ := (HD3 a 0 0).2
    obtain ⟨Mg, _, hMg⟩ := Quad2IbpSub.rep_ae_bound_of_mem_D hP1 (hyp.1 a)
    have hDub : ∀ᵐ x ∂(cellMeasure p.period), ‖GEQDu p z g a x‖ ≤ Cde + Mg := by
      filter_upwards [hMg] with x hx
      show ‖dy a (p.eFun (p.coord z)) x + rep (g a) x.1 x.2‖ ≤ Cde + Mg
      exact (norm_add_le _ _).trans (add_le_add (hCde x) hx)
    exact memLp_top_of_bound (hsDu a).aestronglyMeasurable (Cde + Mg) hDub
  have T1 : ∀ m i : Fin 3, MemLp (fun x => GEQD3u p z t m l j x m * p.uOf z x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun m i => MemLp.mul (memLp_coord' hUinf i) (memLp_coord' (hD3u m l j) m)
  have T2 : ∀ m i : Fin 3, MemLp (fun x => GEQDdu p z g k m l x m * GEQDu p z g j x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun m i => MemLp.mul (memLp_coord' (hDuInf j) i) (memLp_coord' (hDDu m l) m)
  have T3 : ∀ m i : Fin 3, MemLp (fun x => GEQDdu p z g k m j x m * GEQDu p z g l x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun m i => MemLp.mul (memLp_coord' (hDuInf l) i) (memLp_coord' (hDDu m j) m)
  have T4 : ∀ m i : Fin 3, MemLp (fun x => GEQDu p z g m x m * GEQDdu p z g k l j x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun m i => MemLp.mul (memLp_coord' (hDDu l j) i) (memLp_coord' (hDuInf m) m)
  have T5 : ∀ m i : Fin 3, MemLp (fun x => GEQDdu p z g k l j x m * GEQDu p z g m x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun m i => MemLp.mul (memLp_coord' (hDuInf m) i) (memLp_coord' (hDDu l j) m)
  have T6 : ∀ m i : Fin 3, MemLp (fun x => GEQDu p z g l x m * GEQDdu p z g k m j x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun m i => MemLp.mul (memLp_coord' (hDDu m j) i) (memLp_coord' (hDuInf l) m)
  have T7 : ∀ m i : Fin 3, MemLp (fun x => GEQDu p z g j x m * GEQDdu p z g k m l x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun m i => MemLp.mul (memLp_coord' (hDDu m l) i) (memLp_coord' (hDuInf j) m)
  have T8 : ∀ m i : Fin 3, MemLp (fun x => p.uOf z x m * GEQD3u p z t m l j x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    fun m i => MemLp.mul (memLp_coord' (hD3u m l j) i) (memLp_coord' hUinf m)
  have hcomp : ∀ i : Fin 3, MemLp (fun x => GEQuadField2 p z g k t j l x i)
      UnforcedLeray.B0412.q0E (cellMeasure p.period) := by
    intro i
    have hm : ∀ m ∈ (Finset.univ : Finset (Fin 3)),
        MemLp (fun x =>
          GEQD3u p z t m l j x m * p.uOf z x i + GEQDdu p z g k m l x m * GEQDu p z g j x i +
            GEQDdu p z g k m j x m * GEQDu p z g l x i + GEQDu p z g m x m * GEQDdu p z g k l j x i +
            GEQDdu p z g k l j x m * GEQDu p z g m x i + GEQDu p z g l x m * GEQDdu p z g k m j x i +
            GEQDu p z g j x m * GEQDdu p z g k m l x i + p.uOf z x m * GEQD3u p z t m l j x i)
          UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
      fun m _ =>
        (((((((T1 m i).add (T2 m i)).add (T3 m i)).add (T4 m i)).add (T5 m i)).add (T6 m i)).add
          (T7 m i)).add (T8 m i)
    have hs := memLp_finsetSum Finset.univ hm
    have hfun : (fun x => GEQuadField2 p z g k t j l x i) = fun x =>
        ∑ m ∈ Finset.univ,
          (GEQD3u p z t m l j x m * p.uOf z x i + GEQDdu p z g k m l x m * GEQDu p z g j x i +
            GEQDdu p z g k m j x m * GEQDu p z g l x i + GEQDu p z g m x m * GEQDdu p z g k l j x i +
            GEQDdu p z g k l j x m * GEQDu p z g m x i + GEQDu p z g l x m * GEQDdu p z g k m j x i +
            GEQDu p z g j x m * GEQDdu p z g k m l x i + p.uOf z x m * GEQD3u p z t m l j x i) :=
      funext fun x => hGQ2 i x
    rw [hfun]
    exact hs
  have hL : MemLp (GEQuadField2 p z g k t j l) UnforcedLeray.B0412.q0E (cellMeasure p.period) :=
    MeasureTheory.memLp_piLp_iff.2 hcomp
  have hq0 : UnforcedLeray.B0412.q0E ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ UnforcedLeray.B0412.q0E))
  have hfin : ∫⁻ τ in Ioc (0 : ℝ) p.period, ∫⁻ y, ‖GEQuadField2 p z g k t j l (τ, y)‖ₑ ^
      UnforcedLeray.B0412.q0E.toReal < ⊤ := by
    have h1 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0
      UnforcedLeray.B0412.q0E_ne_top).1 hL.eLpNorm_lt_top
    have hae : AEMeasurable (fun x => ‖GEQuadField2 p z g k t j l x‖ₑ ^
        UnforcedLeray.B0412.q0E.toReal) (cellMeasure p.period) :=
      (hL.aestronglyMeasurable.enorm).pow_const _
    have h2 : ∫⁻ x, ‖GEQuadField2 p z g k t j l x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal
        ∂(cellMeasure p.period) = ∫⁻ τ in Ioc (0 : ℝ) p.period, ∫⁻ y,
          ‖GEQuadField2 p z g k t j l (τ, y)‖ₑ ^ UnforcedLeray.B0412.q0E.toReal :=
      lintegral_prod _ hae
    rwa [← h2]
  obtain ⟨F, hF⟩ := UnforcedLeray.Short.PartIIa.periodicFieldToYq_proof
    UnforcedLeray.B0412.q0E (by simp [UnforcedLeray.B0412.q0E]) p.period _ hSM
    (ae_of_all _ fun τ => ae_of_all _ fun y => hperF (τ, y)) hfin
  refine ⟨F, fun Φ hΦ => ?_⟩
  rw [UnforcedLeray.Cons.C03.Concrete.phasePair_eq_pairF_rep hΦ F]
  unfold pairF phaseInt
  congr 1
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  have h2 : ∀ᵐ τ : ℝ, (fun y => rep F τ y) =ᵐ[volume]
      (fun y => GEQuadField2 p z g k t j l (τ, y)) := by
    filter_upwards [hF.slice] with τ hτ
    exact (UnforcedLeray.Cons.C03.Concrete.rep_slice F τ).trans hτ.symm
  filter_upwards [h2] with τ hτ
  exact integral_congr_ae (by filter_upwards [hτ] with y hy; simp only [hy])

end UnforcedLeray.Short.PartIIIb.Concrete
