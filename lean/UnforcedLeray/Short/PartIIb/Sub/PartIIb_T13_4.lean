import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13

/-!
# Part II-b, task `PartII-b:T13/4`: the graph bound depends on `b` only through its `H_r` class

Source of record: `the November 2 reference manuscript`, lines 1912-1938.

The drafted target `GraphBoundCongr` is false as stated: `Axi.ageμ` lives on `s > 0` and the
`q`-cell `[-c/2, c/2) × ℝ`, so `b =ᵐ[hMeas c r] b'` does not control `b` off the cell (a box
indicator is a counterexample).  The source objects are `c`-periodic (`InHr` includes
`QPeriodic`), so the corrected statement adds `0 < c`, `QPeriodic c b`, `QPeriodic c b'`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set

/-- Corrected `GraphBoundCongr` (SP 1912-1938): periodic profiles. -/
def GraphBoundCongrPer : Prop :=
  ∀ (ν c r C : ℝ) (F b b' : CProf), 0 < c → QPeriodic c b → QPeriodic c b' →
    b =ᵐ[hMeas c r] b' → GraphBound ν c r 0 C F b' → GraphBound ν c r 0 C F b

namespace CongrHelp

/-- Translation by `k` periods in `q`. -/
def T (c : ℝ) (k : ℤ) (x : Coord) : Coord := x + (0, ((k : ℝ) * c, 0))

theorem mp_T (c : ℝ) (k : ℤ) :
    MeasurePreserving (T c k) (volume : Measure Coord) volume :=
  measurePreserving_add_right volume _

theorem qShift_eq (c : ℝ) : qShift c = T c 1 := by
  funext x
  ext <;> simp [qShift, T]

theorem T_add (c : ℝ) (j k : ℤ) (x : Coord) : T c j (T c k x) = T c (j + k) x := by
  ext <;> simp [T] <;> ring

/-- Periodicity of an a.e.-periodic profile under all integer multiples of the period. -/
theorem ae_T {c : ℝ} {b : CProf} (hb : QPeriodic c b) (k : ℤ) :
    ∀ᵐ x : Coord, 0 < x.1 → b (T c k x) = b x := by
  have hb' : ∀ᵐ x : Coord, 0 < x.1 → b (qShift c x) = b x :=
    (ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)).1 hb
  have pull : ∀ (j : ℤ) {p : Coord → Prop}, (∀ᵐ x : Coord, p x) → ∀ᵐ x : Coord, p (T c j x) :=
    fun j p hp => (mp_T c j).quasiMeasurePreserving.ae hp
  have h1T : ∀ (j : ℤ) (x : Coord), (T c j x).1 = x.1 := fun j x => by simp [T]
  induction k using Int.induction_on with
  | zero =>
    exact Filter.Eventually.of_forall fun x _ => by
      have : T c 0 x = x := by simp [T]
      rw [this]
  | succ n ih =>
    have h1 : ∀ᵐ x : Coord, 0 < (T c n x).1 → b (qShift c (T c n x)) = b (T c n x) :=
      pull n hb'
    filter_upwards [h1, ih] with x h1 h2 hx
    rw [h1T] at h1
    rw [qShift_eq, T_add] at h1
    have e : (1 + (n : ℤ)) = (n : ℤ) + 1 := add_comm _ _
    rw [e] at h1
    exact (h1 hx).trans (h2 hx)
  | pred n ih =>
    have h1 : ∀ᵐ x : Coord, 0 < (T c (-n - 1) x).1 →
        b (qShift c (T c (-n - 1) x)) = b (T c (-n - 1) x) :=
      pull (-n - 1) hb'
    filter_upwards [h1, ih] with x h1 h2 hx
    rw [h1T] at h1
    rw [qShift_eq, T_add] at h1
    have e : (1 + (-(n : ℤ) - 1)) = -(n : ℤ) := by ring
    rw [e] at h1
    exact (h1 hx).symm.trans (h2 hx)

/-- `ageμ`-null sets are Lebesgue-null on the open half-cell `s > 0`, `q ∈ cell`. -/
theorem volume_null_of_ageμ {c a : ℝ} (hc : 0 < c) {Z : Set Coord} (hZ : Axi.ageμ c a Z = 0) :
    ∃ M : Set Coord, Z ⊆ M ∧ MeasurableSet M ∧
      volume (M ∩ (Ioi (0 : ℝ) ×ˢ Axi.qCell c)) = 0 := by
  obtain ⟨M, hZM, hM, hM0⟩ := exists_measurable_superset_of_null hZ
  refine ⟨M, hZM, hM, ?_⟩
  have hA := Axi.measurableSet_halfCell c
  have h := Axi.lintegral_ageμ hc a (f := M.indicator 1) (measurable_one.indicator hM)
  rw [lintegral_indicator_one hM, hM0] at h
  have hmeas : Measurable fun p : Coord =>
      ENNReal.ofReal (c⁻¹ * p.1 ^ a) * M.indicator (1 : Coord → ENNReal) p :=
    (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (measurable_fst.pow_const a))).mul
      (measurable_one.indicator hM)
  have h0 := (lintegral_eq_zero_iff hmeas).1 h.symm
  have hae : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Axi.qCell c)), p ∉ M := by
    filter_upwards [h0, ae_restrict_mem hA] with p hp hpA
    by_contra hpM
    have hw : 0 < ENNReal.ofReal (c⁻¹ * p.1 ^ a) :=
      ENNReal.ofReal_pos.2 (mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos hpA.1 a))
    rw [Set.indicator_of_mem hpM, Pi.one_apply, mul_one] at hp
    exact hw.ne' hp
  have := measure_eq_zero_iff_ae_notMem.2 hae
  rwa [Measure.restrict_apply hM] at this

/-- Two a.e.-`q`-periodic profiles that agree `ageμ`-a.e. agree Lebesgue-a.e. on `s > 0`. -/
theorem ae_volume_of_ageμ {c a : ℝ} (hc : 0 < c) {b b' : CProf} (hb : QPeriodic c b)
    (hb' : QPeriodic c b') (h : b =ᵐ[Axi.ageμ c a] b') :
    ∀ᵐ x : Coord, 0 < x.1 → b x = b' x := by
  obtain ⟨M, hZM, hM, hM0⟩ := volume_null_of_ageμ hc (a := a) (Z := {x | ¬ b x = b' x})
    (ae_iff.1 h)
  have hper : ∀ᵐ x : Coord, 0 < x.1 → ∀ k : ℤ, b (T c k x) = b x ∧ b' (T c k x) = b' x := by
    have := ae_all_iff.2 fun k : ℤ => (ae_T hb k).and (ae_T hb' k)
    filter_upwards [this] with x hx hpos k using ⟨(hx k).1 hpos, (hx k).2 hpos⟩
  have hnull : ∀ k : ℤ, volume (T c (-k) ⁻¹' (M ∩ (Ioi (0 : ℝ) ×ˢ Axi.qCell c))) = 0 :=
    fun k => (mp_T c (-k)).quasiMeasurePreserving.preimage_null hM0
  have hunion : volume (⋃ k : ℤ, T c (-k) ⁻¹' (M ∩ (Ioi (0 : ℝ) ×ˢ Axi.qCell c))) = 0 :=
    measure_iUnion_null hnull
  have hbad := measure_eq_zero_iff_ae_notMem.1 hunion
  filter_upwards [hper, hbad] with x hx hxb hpos
  replace hx := hx hpos
  by_contra hne
  set k : ℤ := ⌊(x.2.1 + c / 2) / c⌋ with hk
  apply hxb
  refine Set.mem_iUnion.2 ⟨k, ?_⟩
  have hk1 : (k : ℝ) ≤ (x.2.1 + c / 2) / c := Int.floor_le _
  have hk2 : (x.2.1 + c / 2) / c < k + 1 := Int.lt_floor_add_one _
  have hk1' : (k : ℝ) * c ≤ x.2.1 + c / 2 := by
    rwa [le_div_iff₀ hc] at hk1
  have hk2' : x.2.1 + c / 2 < ((k : ℝ) + 1) * c := by
    rwa [div_lt_iff₀ hc] at hk2
  obtain ⟨e1, e2⟩ := hx (-k)
  refine ⟨hZM ?_, ?_⟩
  · intro hy
    apply hne
    rw [e1, e2] at hy
    exact hy
  · refine ⟨?_, ?_, trivial⟩
    · simpa [T] using hpos
    · simp only [T, Prod.fst_add, Prod.snd_add]
      constructor <;> push_cast <;> linarith

/-- The transpose of a test supported in `s > 0` vanishes outside `s > 0`. -/
theorem coordTranspose_eq_zero {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {φ : Coord → ℝ}
    (hφ : IsCoordTest φ) {x : Coord} (hx : ¬ 0 < x.1) : coordTranspose v d φ x = 0 := by
  have hxt : x ∉ tsupport φ := fun h => hx (hφ.supp h).1
  have hev : φ =ᶠ[nhds x] 0 := by
    have := notMem_tsupport_iff_eventuallyEq.1 hxt
    exact this
  have hφx : φ x = 0 := hev.self_of_nhds
  have hj : ∀ j : Fin 3, cpd j (fun y => v y j * φ y) x = 0 := by
    intro j
    have : (fun y => v y j * φ y) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [hev] with y hy
      simp [hy]
    unfold cpd
    rw [this.fderiv_eq]
    simp
  simp [coordTranspose, hj, hφx]

theorem hasWeakFO_congr {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u u' g : Coord → ℂ}
    (h : ∀ᵐ x : Coord, 0 < x.1 → u x = u' x) (hu : HasWeakFO v d u' g) : HasWeakFO v d u g := by
  have key : ∀ φ, IsCoordTest φ →
      (fun x => u x * (coordTranspose v d φ x : ℂ)) =ᵐ[volume]
        fun x => u' x * (coordTranspose v d φ x : ℂ) := by
    intro φ hφ
    filter_upwards [h] with x hx
    by_cases hp : 0 < x.1
    · simp [hx hp]
    · simp [coordTranspose_eq_zero hφ hp]
  refine ⟨fun φ hφ => ⟨?_, (hu.1 φ hφ).2⟩, fun φ hφ => ?_⟩
  · exact ((hu.1 φ hφ).1).congr (key φ hφ).symm
  · rw [hu.2 φ hφ]
    exact integral_congr_ae (key φ hφ).symm

end CongrHelp

theorem graphBoundCongrPer : GraphBoundCongrPer := by
  intro ν c r C F b b' hc hb hb' hbb' hg
  have hae : ∀ᵐ x : Coord, 0 < x.1 → b x = b' x :=
    CongrHelp.ae_volume_of_ageμ hc hb hb' hbb'
  obtain ⟨Sb, Qb, Eb, h1, h2, h3, hn⟩ := hg
  refine ⟨Sb, Qb, Eb, ?_, ?_, ?_, ?_⟩
  · intro i
    exact CongrHelp.hasWeakFO_congr (by filter_upwards [hae] with x hx hp; rw [hx hp]) (h1 i)
  · intro i
    exact CongrHelp.hasWeakFO_congr (by filter_upwards [hae] with x hx hp; rw [hx hp]) (h2 i)
  · intro i
    exact CongrHelp.hasWeakFO_congr (by filter_upwards [hae] with x hx hp; rw [hx hp]) (h3 i)
  · have : hNorm c r b = hNorm c r b' := eLpNorm_congr_ae hbb'
    rw [this]
    exact hn

/-- `flatGraphBound_of` with the corrected congruence step. -/
theorem flatGraphBound_of_per (h1 : FlatGraphExists) (h2 : FlatResponseSub) (h3 : FlatClassSub)
    (h4 : GraphBoundCongrPer) : FlatGraphBound := by
  intro r hr hr3 μ ha
  obtain ⟨C, hC⟩ := h1 r hr hr3 μ ha
  refine ⟨C, fun ν c hν hc F hF b hb hbc => ?_⟩
  obtain ⟨b', hb', hc', hg'⟩ := hC ν c hν hc F hF
  have h0 : b - b' =ᵐ[hMeas c r] 0 :=
    flat_unique hc hν hr hr3 ha (b - b') (h3 c r b b' hbc hc') (h2 ν μ F b b' hb hb')
  refine h4 ν c r C F b b' hc hbc.inHr.periodic hc'.inHr.periodic ?_ hg'
  filter_upwards [h0] with x hx
  exact sub_eq_zero.mp hx


end UnforcedLeray.Short.IIb

end
