import UnforcedLeray.Short.PartI.Sub.PartI_T09.JetL2Bridge
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation

/-!
# `PartI:T09` leaf 3b: the sup bridge (`JetSupBridge`, source lines 366-374)

Apply `CylSupInterp` (conjunct 1 of `cylinder_interpolation_uniform`) to the scalar word
derivatives `g = wordComp w f k`, `|w| = j`. Their `L²`, `D g`, `D² g` norms are bounded by the
jet energies `√J_j`, `√J_{j+1}`, `√J_{j+2}` (`jl2_energy_le` and `jsb_scalar_jet`), which gives
`|g| ≤ supRhs`. The second conjunct sums the first over the coordinate words.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

lemma jsb_mem_wordsOfLength {n : ℕ} {v : List Bool} : v ∈ wordsOfLength n ↔ v.length = n := by
  unfold wordsOfLength
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro h
    subst h
    exact ⟨v.get, List.ofFn_get v⟩

lemma jsb_derivWord_append (u w : List Bool) (h : Plane → ℝ) :
    B0151.derivWord u (B0151.derivWord w h) = B0151.derivWord (u ++ w) h := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b with
    | false => simp only [List.cons_append, B0151.derivWord, ih]
    | true => simp only [List.cons_append, B0151.derivWord, ih]

lemma jsb_periodic_partialX {c : ℝ} {h : Plane → ℝ} (hp : Cyl.IsPeriodic c h) :
    Cyl.IsPeriodic c (GaussianVortex.partialX h) := by
  unfold Cyl.IsPeriodic at hp ⊢
  intro z
  have hd : deriv (fun x : ℝ => h (x, z.2)) (z.1 + c) = deriv (fun x : ℝ => h (x, z.2)) z.1 := by
    rw [← deriv_comp_add_const]
    congr 1
    funext x
    exact hp (x, z.2)
  exact hd

lemma jsb_periodic_partialY {c : ℝ} {h : Plane → ℝ} (hp : Cyl.IsPeriodic c h) :
    Cyl.IsPeriodic c (GaussianVortex.partialY h) := by
  unfold Cyl.IsPeriodic at hp ⊢
  intro z
  have hf : (fun y : ℝ => h (z.1 + c, y)) = (fun y : ℝ => h (z.1, y)) := by
    funext y
    exact hp (z.1, y)
  show deriv (fun y : ℝ => h (z.1 + c, y)) z.2 = deriv (fun y : ℝ => h (z.1, y)) z.2
  rw [hf]

lemma jsb_periodic_derivWord (c : ℝ) (w : List Bool) :
    ∀ h : Plane → ℝ, Cyl.IsPeriodic c h → Cyl.IsPeriodic c (B0151.derivWord w h) := by
  induction w with
  | nil => intro h hp; exact hp
  | cons b w ih =>
    intro h hp
    cases b with
    | false => exact jsb_periodic_partialY (ih h hp)
    | true => exact jsb_periodic_partialX (ih h hp)

/-- Generic `L²` bound by a sum of absolute values of finitely many functions. -/
lemma jsb_generic {E : Type*} [NormedAddCommGroup E] (μ : Measure Plane) {ι : Type*}
    (N : Finset ι) (g : ι → Plane → ℝ) (hg : ∀ i ∈ N, MemLp (g i) 2 μ) (J : ℝ)
    (hJ : ∀ i ∈ N, ∫ z, g i z ^ 2 ∂μ ≤ J) (F : Plane → E)
    (hF : ∀ z, ‖F z‖ ≤ ∑ i ∈ N, |g i z|) :
    eLpNorm F 2 μ ≤ ENNReal.ofReal ((N.card : ℝ) * Real.sqrt J) := by
  have h1 : eLpNorm F 2 μ ≤ eLpNorm (fun z => ∑ i ∈ N, |g i z|) 2 μ := by
    apply eLpNorm_mono
    intro z
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    exact hF z
  have h2 : eLpNorm (fun z => ∑ i ∈ N, |g i z|) 2 μ ≤
      ∑ i ∈ N, eLpNorm (fun z => |g i z|) 2 μ := by
    have := eLpNorm_sum_le (μ := μ) (p := 2)
      (f := fun (i : ι) (z : Plane) => |g i z|) (s := N)
      (fun i hi => by simpa [Real.norm_eq_abs] using (hg i hi).aestronglyMeasurable.norm)
      one_le_two
    simpa only [Finset.sum_fn] using this
  have h3 : ∀ i ∈ N, eLpNorm (fun z => |g i z|) 2 μ ≤ ENNReal.ofReal (Real.sqrt J) := by
    intro i hi
    rw [jl2_abs_eLpNorm μ (g i) (hg i hi)]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hJ i hi))
  calc eLpNorm F 2 μ ≤ ∑ i ∈ N, eLpNorm (fun z => |g i z|) 2 μ := h1.trans h2
    _ ≤ ∑ i ∈ N, ENNReal.ofReal (Real.sqrt J) := Finset.sum_le_sum h3
    _ = (N.card : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt J) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal ((N.card : ℝ) * Real.sqrt J) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The `l`-th jet of a scalar word derivative of order `j`, in cell `L²`. -/
lemma jsb_scalar_jet (c : ℝ) (j l : ℕ) (f : Plane → Vec) (hf : CellSmoothL2 c f)
    (w : List Bool) (hw : w.length = j) (k : Fin 2) :
    Train.cellL2 c (Train.jet l (wordComp w f k)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ l * Real.sqrt (jetEnergy c (j + l) f)) := by
  have hk : ContDiff ℝ ∞ (fun x => f x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hf.1
  have hgs : ContDiff ℝ ∞ (wordComp w f k) := B0151.contDiff_derivWord hk w
  have hpt : ∀ z, ‖iteratedFDeriv ℝ l (wordComp w f k) z‖ ≤
      ∑ u ∈ wordsOfLength l, |wordComp (u ++ w) f k z| := by
    intro z
    have h := (cylJetWord_proof (wordComp w f k) hgs l z).2
    refine h.trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro u _
    show |B0151.derivWord u (B0151.derivWord w (fun x => f x k)) z| =
      |B0151.derivWord (u ++ w) (fun x => f x k) z|
    rw [jsb_derivWord_append]
  have hJ : ∀ u ∈ wordsOfLength l,
      ∫ z, wordComp (u ++ w) f k z ^ 2 ∂(Cyl.cellμ c) ≤ jetEnergy c (j + l) f := by
    intro u hu
    apply jl2_energy_le c (j + l) f hf (u ++ w) _ k
    rw [jsb_mem_wordsOfLength]
    have hu' := jsb_mem_wordsOfLength.1 hu
    simp only [List.length_append]
    omega
  have hbound := jsb_generic (Cyl.cellμ c) (wordsOfLength l) (fun u z => wordComp (u ++ w) f k z)
    (fun u _ => hf.2.2 (u ++ w) k) (jetEnergy c (j + l) f) hJ
    (fun z => iteratedFDeriv ℝ l (wordComp w f k) z) hpt
  have hcard : ((wordsOfLength l).card : ℝ) ≤ 2 ^ l := by
    have h1 : (wordsOfLength l).card ≤ 2 ^ l := by
      unfold wordsOfLength
      calc _ ≤ (Finset.univ : Finset (Fin l → Bool)).card := Finset.card_image_le
        _ = 2 ^ l := by simp
    exact_mod_cast h1
  calc Train.cellL2 c (Train.jet l (wordComp w f k))
      = eLpNorm (fun z => iteratedFDeriv ℝ l (wordComp w f k) z) 2 (Cyl.cellμ c) := rfl
    _ ≤ _ := hbound
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ l * Real.sqrt (jetEnergy c (j + l) f)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _))

lemma jsb_memLp_jet (c : ℝ) (l : ℕ) (g : Plane → ℝ) (hgs : ContDiff ℝ ∞ g) (B : ENNReal)
    (hB : Train.cellL2 c (Train.jet l g) ≤ B) (hB' : B ≠ ⊤) :
    MemLp (Train.jet l g) 2 (Cyl.cellμ c) := by
  have hl : (l : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcont : Continuous (fun z => iteratedFDeriv ℝ l g z) := hgs.continuous_iteratedFDeriv hl
  exact ⟨hcont.aestronglyMeasurable, lt_of_le_of_lt hB (lt_top_iff_ne_top.2 hB')⟩

lemma jsb_supRhs_nonneg {c : ℝ} (hc : 0 ≤ c) (Jj Jj1 Jj2 : ℝ) :
    0 ≤ (Real.sqrt Jj * Real.sqrt Jj2) ^ (1 / 2 : ℝ) +
      c ^ (-(1 / 2 : ℝ)) * (Real.sqrt Jj * Real.sqrt Jj1) ^ (1 / 2 : ℝ) := by
  have h1 : 0 ≤ (Real.sqrt Jj * Real.sqrt Jj2) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) _
  have h2 : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc _
  have h3 : 0 ≤ (Real.sqrt Jj * Real.sqrt Jj1) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) _
  have := mul_nonneg h2 h3
  linarith

lemma jsb_supRhs_mono {c : ℝ} (hc : 0 ≤ c) {C C' : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C')
    (Jj Jj1 Jj2 : ℝ) : supRhs C c Jj Jj1 Jj2 ≤ supRhs C' c Jj Jj1 Jj2 := by
  unfold supRhs
  exact mul_le_mul_of_nonneg_right hCC (jsb_supRhs_nonneg hc Jj Jj1 Jj2)

lemma jsb_rpow_four : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma jsb_rpow_two_le : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
  calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

theorem jetSupBridge_proof : JetSupBridge := by
  intro j
  have hSup : CylSupInterp := (cylinder_interpolation_uniform : CylSupInterp ∧ CylGN).1
  obtain ⟨Cs, hCs0, hCs⟩ := hSup
  have h2j : (1 : ℝ) ≤ 2 * 2 ^ j := by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    linarith
  refine ⟨2 * 2 ^ j * (2 * Cs), mul_nonneg (by positivity) (mul_nonneg two_pos.le hCs0), ?_⟩
  intro c hc f hf
  have hc0 : 0 ≤ c := by linarith
  have hcs1 : 0 ≤ 2 * Cs := mul_nonneg two_pos.le hCs0
  -- the scalar bound for coordinate words of length `j`
  have core : ∀ w : List Bool, w.length = j → ∀ (k : Fin 2) (z : Plane),
      |wordComp w f k z| ≤
        supRhs (2 * Cs) c (jetEnergy c j f) (jetEnergy c (j + 1) f) (jetEnergy c (j + 2) f) := by
    intro w hw k z
    have hk : ContDiff ℝ ∞ (fun x => f x k) :=
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hf.1
    have hgs : ContDiff ℝ ∞ (wordComp w f k) := B0151.contDiff_derivWord hk w
    have hper : Cyl.IsPeriodic c (wordComp w f k) := by
      apply jsb_periodic_derivWord c w
      unfold Cyl.IsPeriodic
      intro y
      exact congrArg (fun v => v k) (hf.2.1 y)
    have hL2 : MemLp (wordComp w f k) 2 (Cyl.cellμ c) := hf.2.2 w k
    have hA : eLpNorm (wordComp w f k) 2 (Cyl.cellμ c) ≤
        ENNReal.ofReal (Real.sqrt (jetEnergy c j f)) := by
      have e : eLpNorm (fun z => |wordComp w f k z|) 2 (Cyl.cellμ c) =
          eLpNorm (wordComp w f k) 2 (Cyl.cellμ c) := by
        have := eLpNorm_norm (p := 2) (μ := Cyl.cellμ c) (wordComp w f k)
        simpa only [Real.norm_eq_abs] using this
      rw [← e, jl2_abs_eLpNorm _ _ hL2]
      exact ENNReal.ofReal_le_ofReal
        (Real.sqrt_le_sqrt (jl2_energy_le c j f hf w (jsb_mem_wordsOfLength.2 hw) k))
    have B1 := jsb_scalar_jet c j 1 f hf w hw k
    have B2 := jsb_scalar_jet c j 2 f hf w hw k
    have M1 : MemLp (Train.jet 1 (wordComp w f k)) 2 (Cyl.cellμ c) :=
      jsb_memLp_jet c 1 _ hgs _ B1 ENNReal.ofReal_ne_top
    have M2 : MemLp (Train.jet 2 (wordComp w f k)) 2 (Cyl.cellμ c) :=
      jsb_memLp_jet c 2 _ hgs _ B2 ENNReal.ofReal_ne_top
    have hpoint := hCs c hc (wordComp w f k) hgs hper hL2 M1 M2 z
    have hY2 : (eLpNorm (wordComp w f k) 2 (Cyl.cellμ c) *
        Train.cellL2 c (Train.jet 2 (wordComp w f k))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal ((Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 2 *
          Real.sqrt (jetEnergy c (j + 2) f))) ^ (1 / 2 : ℝ)) := by
      calc (eLpNorm (wordComp w f k) 2 (Cyl.cellμ c) *
            Train.cellL2 c (Train.jet 2 (wordComp w f k))) ^ (1 / 2 : ℝ)
          ≤ (ENNReal.ofReal (Real.sqrt (jetEnergy c j f)) *
              ENNReal.ofReal ((2 : ℝ) ^ 2 * Real.sqrt (jetEnergy c (j + 2) f))) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow (mul_le_mul' hA B2) (by norm_num)
        _ = ENNReal.ofReal ((Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 2 *
              Real.sqrt (jetEnergy c (j + 2) f))) ^ (1 / 2 : ℝ)) := by
            rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
              ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
                (by norm_num)]
    have hY1 : (eLpNorm (wordComp w f k) 2 (Cyl.cellμ c) *
        Train.cellL2 c (Train.jet 1 (wordComp w f k))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal ((Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 1 *
          Real.sqrt (jetEnergy c (j + 1) f))) ^ (1 / 2 : ℝ)) := by
      calc (eLpNorm (wordComp w f k) 2 (Cyl.cellμ c) *
            Train.cellL2 c (Train.jet 1 (wordComp w f k))) ^ (1 / 2 : ℝ)
          ≤ (ENNReal.ofReal (Real.sqrt (jetEnergy c j f)) *
              ENNReal.ofReal ((2 : ℝ) ^ 1 * Real.sqrt (jetEnergy c (j + 1) f))) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow (mul_le_mul' hA B1) (by norm_num)
        _ = ENNReal.ofReal ((Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 1 *
              Real.sqrt (jetEnergy c (j + 1) f))) ^ (1 / 2 : ℝ)) := by
            rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
              ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
                (by norm_num)]
    have hnn1 : 0 ≤ (Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 2 *
        Real.sqrt (jetEnergy c (j + 2) f))) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) _
    have hnn2 : 0 ≤ (Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 1 *
        Real.sqrt (jetEnergy c (j + 1) f))) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) _
    have hcnn : 0 ≤ Cs * c ^ (-(1 / 2 : ℝ)) := mul_nonneg hCs0 (Real.rpow_nonneg hc0 _)
    have hfin : ‖wordComp w f k z‖ₑ ≤ ENNReal.ofReal (Cs *
        (Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 2 * Real.sqrt (jetEnergy c (j + 2) f))) ^
          (1 / 2 : ℝ) + Cs * c ^ (-(1 / 2 : ℝ)) * (Real.sqrt (jetEnergy c j f) *
          ((2 : ℝ) ^ 1 * Real.sqrt (jetEnergy c (j + 1) f))) ^ (1 / 2 : ℝ)) := by
      calc ‖wordComp w f k z‖ₑ ≤ ENNReal.ofReal Cs * (eLpNorm (wordComp w f k) 2 (Cyl.cellμ c) *
            Train.cellL2 c (Train.jet 2 (wordComp w f k))) ^ (1 / 2 : ℝ) +
            ENNReal.ofReal (Cs * c ^ (-(1 / 2 : ℝ))) * (eLpNorm (wordComp w f k) 2
            (Cyl.cellμ c) * Train.cellL2 c (Train.jet 1 (wordComp w f k))) ^ (1 / 2 : ℝ) :=
            hpoint
        _ ≤ ENNReal.ofReal Cs * ENNReal.ofReal ((Real.sqrt (jetEnergy c j f) *
              ((2 : ℝ) ^ 2 * Real.sqrt (jetEnergy c (j + 2) f))) ^ (1 / 2 : ℝ)) +
            ENNReal.ofReal (Cs * c ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal ((Real.sqrt
              (jetEnergy c j f) * ((2 : ℝ) ^ 1 * Real.sqrt (jetEnergy c (j + 1) f))) ^
              (1 / 2 : ℝ)) :=
            add_le_add (by gcongr) (by gcongr)
        _ = ENNReal.ofReal (Cs *
            (Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 2 * Real.sqrt (jetEnergy c (j + 2) f))) ^
              (1 / 2 : ℝ) + Cs * c ^ (-(1 / 2 : ℝ)) * (Real.sqrt (jetEnergy c j f) *
              ((2 : ℝ) ^ 1 * Real.sqrt (jetEnergy c (j + 1) f))) ^ (1 / 2 : ℝ)) := by
            rw [← ENNReal.ofReal_mul hCs0, ← ENNReal.ofReal_mul hcnn,
              ← ENNReal.ofReal_add (mul_nonneg hCs0 hnn1) (mul_nonneg hcnn hnn2)]
    have hreal : ‖wordComp w f k z‖ ≤ Cs *
        (Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 2 * Real.sqrt (jetEnergy c (j + 2) f))) ^
          (1 / 2 : ℝ) + Cs * c ^ (-(1 / 2 : ℝ)) * (Real.sqrt (jetEnergy c j f) *
          ((2 : ℝ) ^ 1 * Real.sqrt (jetEnergy c (j + 1) f))) ^ (1 / 2 : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg hCs0 hnn1)
        (mul_nonneg hcnn hnn2))).1 (by rw [ofReal_norm_eq_enorm]; exact hfin)
    have hPnn : 0 ≤ Real.sqrt (jetEnergy c j f) * Real.sqrt (jetEnergy c (j + 2) f) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hQnn : 0 ≤ Real.sqrt (jetEnergy c j f) * Real.sqrt (jetEnergy c (j + 1) f) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hY2e : (Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 2 *
        Real.sqrt (jetEnergy c (j + 2) f))) ^ (1 / 2 : ℝ) =
        2 * (Real.sqrt (jetEnergy c j f) * Real.sqrt (jetEnergy c (j + 2) f)) ^ (1 / 2 : ℝ) := by
      rw [show Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 2 * Real.sqrt (jetEnergy c (j + 2) f))
          = 4 * (Real.sqrt (jetEnergy c j f) * Real.sqrt (jetEnergy c (j + 2) f)) by ring,
        Real.mul_rpow (by norm_num) hPnn, jsb_rpow_four]
    have hY1le : (Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 1 *
        Real.sqrt (jetEnergy c (j + 1) f))) ^ (1 / 2 : ℝ) ≤
        2 * (Real.sqrt (jetEnergy c j f) * Real.sqrt (jetEnergy c (j + 1) f)) ^ (1 / 2 : ℝ) := by
      rw [show Real.sqrt (jetEnergy c j f) * ((2 : ℝ) ^ 1 *
          Real.sqrt (jetEnergy c (j + 1) f))
          = 2 * (Real.sqrt (jetEnergy c j f) * Real.sqrt (jetEnergy c (j + 1) f)) by ring,
        Real.mul_rpow (by norm_num) hQnn]
      exact mul_le_mul_of_nonneg_right jsb_rpow_two_le (Real.rpow_nonneg hQnn _)
    unfold supRhs
    have hcnn' : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0 _
    calc |wordComp w f k z| = ‖wordComp w f k z‖ := (Real.norm_eq_abs _).symm
      _ ≤ Cs * (2 * (Real.sqrt (jetEnergy c j f) * Real.sqrt (jetEnergy c (j + 2) f)) ^
            (1 / 2 : ℝ)) + Cs * c ^ (-(1 / 2 : ℝ)) * (2 * (Real.sqrt (jetEnergy c j f) *
            Real.sqrt (jetEnergy c (j + 1) f)) ^ (1 / 2 : ℝ)) := by
          rw [hY2e] at hreal
          refine hreal.trans (add_le_add le_rfl ?_)
          exact mul_le_mul_of_nonneg_left hY1le hcnn
      _ = 2 * Cs * ((Real.sqrt (jetEnergy c j f) * Real.sqrt (jetEnergy c (j + 2) f)) ^
            (1 / 2 : ℝ) + c ^ (-(1 / 2 : ℝ)) * (Real.sqrt (jetEnergy c j f) *
            Real.sqrt (jetEnergy c (j + 1) f)) ^ (1 / 2 : ℝ)) := by ring
  have hCtot : 2 * Cs ≤ 2 * 2 ^ j * (2 * Cs) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h2j) hcs1]
  refine ⟨fun w hw k z => (core w hw k z).trans (jsb_supRhs_mono hc0 hcs1 hCtot _ _ _), ?_⟩
  unfold B0277.supNormD
  apply iSup_le
  intro z
  rw [← ofReal_norm_eq_enorm]
  apply ENNReal.ofReal_le_ofReal
  have hcardI : ((wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) ≤ 2 * 2 ^ j := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have hW : (wordsOfLength j).card ≤ 2 ^ j := by
      unfold wordsOfLength
      calc _ ≤ (Finset.univ : Finset (Fin j → Bool)).card := Finset.card_image_le
        _ = 2 ^ j := by simp
    have hW' : ((wordsOfLength j).card : ℝ) ≤ 2 ^ j := by exact_mod_cast hW
    push_cast
    linarith
  have hsupNN : 0 ≤ supRhs (2 * Cs) c (jetEnergy c j f) (jetEnergy c (j + 1) f)
      (jetEnergy c (j + 2) f) := by
    unfold supRhs
    exact mul_nonneg hcs1 (jsb_supRhs_nonneg hc0 _ _ _)
  calc ‖iteratedFDeriv ℝ j f z‖
      ≤ ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)), |wordComp i.1 f i.2 z| :=
        jl2_pointwise j f hf.1 z
    _ ≤ ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
        supRhs (2 * Cs) c (jetEnergy c j f) (jetEnergy c (j + 1) f) (jetEnergy c (j + 2) f) :=
        Finset.sum_le_sum (fun i hi => by
          rw [Finset.mem_product] at hi
          exact core i.1 (jsb_mem_wordsOfLength.1 hi.1) i.2 z)
    _ = ((wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) *
        supRhs (2 * Cs) c (jetEnergy c j f) (jetEnergy c (j + 1) f) (jetEnergy c (j + 2) f) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * 2 ^ j) * supRhs (2 * Cs) c (jetEnergy c j f) (jetEnergy c (j + 1) f)
        (jetEnergy c (j + 2) f) := mul_le_mul_of_nonneg_right hcardI hsupNN
    _ = supRhs (2 * 2 ^ j * (2 * Cs)) c (jetEnergy c j f) (jetEnergy c (j + 1) f)
        (jetEnergy c (j + 2) f) := by
        unfold supRhs
        ring

end UnforcedLeray.Short.PartI
