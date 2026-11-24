import UnforcedLeray.Short.PartI.Sub.T02_1_3
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.AePeriodicEq
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.CylSmoothDensity
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.CylSmoothSobolevBound
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.ContDiffLimitCauchy

/-!
# Part I, task `PartI:T02/1/3/1`: the Sobolev embedding on the periodic cylinder

Source of record: `the November 2 reference manuscript`, lines 261-288.

The target is `cylSobolevRep : CylSobolevRep` (`Short/PartI/Sub/T02_1_3.lean`, line 68).

## Route

For `x` in `H^{k+3}` take smooth periodic approximants `u n` with `csrOf (u n) → x`
(`cylSmoothDensity`). The Sobolev bound `cylSmoothSobolevBound` controls every classical
derivative of order `≤ k + 1` of `u n - u m` by the distance `dist (csrOf (u n)) (csrOf (u m))`,
so the classical derivatives form uniformly Cauchy sequences. `contDiffLimitCauchy` then gives
a `C^{k+1}` limit `G x`, uniform convergence of all its derivatives of order `≤ k + 1`, and the
bound `‖D^j G x‖ ≤ C ‖x‖` by passing to the limit. Periodicity passes to the pointwise limit.
The weak derivatives of `x` are identified with the classical derivatives of `G x` almost
everywhere on the cell: the `L²` limit of `cellDeriv (csrOf (u n))` agrees a.e. with the
pointwise limit of the classical derivatives along an a.e. convergent subsequence.
Linearity of `x ↦ G x` follows from `aePeriodicEq` (both sides are continuous, periodic and
a.e. equal to the same cell derivative).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

local instance csrFactOne : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

/-! ### The level `k + 3` element of a smooth periodic field -/

/-- The element of the periodic cylinder space `H^{k+3}` carried by a smooth periodic field. -/
def csrOf (c : ℝ) (hc : 0 < c) (k : ℕ) (u : Plane → Vec) (hu : Sob.IsCylSmooth c u) :
    Cyl.H ℝ Cyl.Vec2 c 0 (k + 3) :=
  Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := k + 3) (p := 2)
    hc u hu

/-- The direction list of a word of classical derivatives. -/
def csrDirs (vs : List Plane) : Fin vs.length → Plane := fun i => vs.get i

/-! ### Elementary facts on smooth periodic fields -/

theorem csr_sub {c : ℝ} {u v : Plane → Vec} (hu : Sob.IsCylSmooth c u)
    (hv : Sob.IsCylSmooth c v) : Sob.IsCylSmooth c (fun z => u z - v z) := by
  refine ⟨hu.smooth.sub hv.smooth, fun z => ?_, ?_⟩
  · show u (z + (c, 0)) - v (z + (c, 0)) = u z - v z
    rw [hu.periodic z, hv.periodic z]
  · obtain ⟨R, hR⟩ := hu.bounded
    obtain ⟨S, hS⟩ := hv.bounded
    refine ⟨max R S, fun z hz => ?_⟩
    show u z - v z = 0
    rw [hR z (lt_of_le_of_lt (le_max_left R S) hz), hS z (lt_of_le_of_lt (le_max_right R S) hz),
      sub_zero]

theorem csr_cd {c : ℝ} {f : Plane → Vec} (hf : Sob.IsCylSmooth c f) (N : ℕ) :
    ContDiff ℝ (N : WithTop ℕ∞) f :=
  hf.smooth.of_le (by exact_mod_cast le_top)

theorem csr_per_add {c : ℝ} {f g : Plane → Vec} (hf : Cyl.IsPeriodic c f)
    (hg : Cyl.IsPeriodic c g) : Cyl.IsPeriodic c (f + g) := fun z => by
  simp only [Pi.add_apply, hf z, hg z]

theorem csr_per_smul {c : ℝ} (r : ℝ) {f : Plane → Vec} (hf : Cyl.IsPeriodic c f) :
    Cyl.IsPeriodic c (r • f) := fun z => by
  simp only [Pi.smul_apply, hf z]

theorem csr_word_len (c : ℝ) {k : ℕ} (β : Sob.Idx 2 (k + 1)) :
    ((Sob.cylinder c).word β).length ≤ k + 1 := by
  rw [Sob.TestDomain.length_word]
  have := β.1.isLt
  omega

/-! ### Linearity of `csrOf` and of the cell derivatives -/

theorem csrOf_sub (c : ℝ) (hc : 0 < c) (k : ℕ) {u v : Plane → Vec}
    (hu : Sob.IsCylSmooth c u) (hv : Sob.IsCylSmooth c v) :
    csrOf c hc k (fun z => u z - v z) (csr_sub hu hv) = csrOf c hc k u hu - csrOf c hc k v hv := by
  unfold csrOf
  apply Sob.W.value_injective
  rw [map_sub]
  apply Lp.ext
  filter_upwards [
    Sob.W.value_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := k + 3)
      (p := 2) hc (fun z => u z - v z) (csr_sub hu hv),
    Sob.W.value_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := k + 3)
      (p := 2) hc u hu,
    Sob.W.value_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := k + 3)
      (p := 2) hc v hv,
    Lp.coeFn_sub (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (k + 3) 2
      (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := k + 3)
        (p := 2) hc u hu))
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (k + 3) 2
      (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := k + 3)
        (p := 2) hc v hv))] with z h1 h2 h3 h4
  simp only [Pi.sub_apply] at h1 h2 h3 h4
  rw [h1, h4, h2, h3]

theorem csr_cellDeriv_add (c : ℝ) {k : ℕ} (α : Sob.Idx 2 (k + 3))
    (x y : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3)) :
    cellDeriv c α (x + y) =ᵐ[Cyl.cellμ c] cellDeriv c α x + cellDeriv c α y := by
  unfold cellDeriv
  rw [map_add, map_add]
  exact Lp.coeFn_add _ _

theorem csr_cellDeriv_smul (c : ℝ) {k : ℕ} (α : Sob.Idx 2 (k + 3)) (r : ℝ)
    (x : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3)) :
    cellDeriv c α (r • x) =ᵐ[Cyl.cellμ c] r • cellDeriv c α x := by
  unfold cellDeriv
  rw [map_smul, map_smul]
  exact Lp.coeFn_smul r _

/-- Almost everywhere equality transfers along an equality of measures. -/
theorem csr_ae_measure {α β : Type*} [MeasurableSpace α] {μ ν : Measure α} (hμν : μ = ν)
    {f g : α → β}
    (h : f =ᵐ[μ] g) : f =ᵐ[ν] g := by
  subst hμν
  exact h

/-- The measure-preserving identification of the weighted value carrier with the centred cell
`L²` is the identity on representatives. -/
theorem csr_iso_coe (c : ℝ)
    (y : Lp Cyl.Vec2 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))) :
    ⇑(weightedToCellL2Isometry c y) =ᵐ[Cyl.cellμ c] ⇑y := by
  have hMP : MeasurePreserving id (Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  exact Lp.coeFn_compMeasurePreserving y hMP

/-! ### Uniform Cauchy sequences from a Lipschitz bound -/

theorem csr_uc_of_lip {X E γ : Type*} [PseudoMetricSpace X] [PseudoMetricSpace E]
    (F : ℕ → γ → E) (Y : ℕ → X) (K : ℝ) (hY : CauchySeq Y) (s : Set γ)
    (h : ∀ m n : ℕ, ∀ z ∈ s, dist (F m z) (F n z) ≤ K * dist (Y m) (Y n)) :
    UniformCauchySeqOn F atTop s := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hK : (0 : ℝ) < |K| + 1 := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hY (ε / (|K| + 1)) (div_pos hε hK)
  refine ⟨N, fun m hm n hn z hz => ?_⟩
  have hd : dist (Y m) (Y n) < ε / (|K| + 1) := hN m hm n hn
  calc dist (F m z) (F n z) ≤ K * dist (Y m) (Y n) := h m n z hz
    _ ≤ (|K| + 1) * dist (Y m) (Y n) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self K, abs_nonneg K]) dist_nonneg
    _ < (|K| + 1) * (ε / (|K| + 1)) := mul_lt_mul_of_pos_left hd hK
    _ = ε := by field_simp

/-! ### Derivatives of smooth fields as iterated Fréchet derivatives -/

theorem csr_iterD_eq (N : ℕ) (f : Plane → Vec) (hf : ContDiff ℝ (N : WithTop ℕ∞) f)
    (vs : List Plane) : vs.length ≤ N →
      Sob.iterD vs f = fun z => iteratedFDeriv ℝ vs.length f z (csrDirs vs) := by
  induction vs with
  | nil =>
    intro _
    funext z
    simp [Sob.iterD, iteratedFDeriv_zero_apply]
  | cons v vs ih =>
    intro hvs
    have hvs' : vs.length + 1 ≤ N := by simpa using hvs
    have ihz := ih (by omega)
    funext z
    change fderiv ℝ (Sob.iterD vs f) z v = iteratedFDeriv ℝ (vs.length + 1) f z (csrDirs (v :: vs))
    rw [ihz]
    have hm : csrDirs (v :: vs) = Fin.cons v (csrDirs vs) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        rfl
    rw [hm, iteratedFDeriv_succ_apply_left]
    simp only [Fin.cons_zero, Fin.tail_cons]
    have hD : ContDiff ℝ (1 : WithTop ℕ∞) (iteratedFDeriv ℝ vs.length f) :=
      hf.iteratedFDeriv_right (m := 1) (i := vs.length)
        (by exact_mod_cast (by omega : 1 + vs.length ≤ N))
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ vs.length f) z :=
      (hD.contDiffAt (x := z)).differentiableAt one_ne_zero
    exact fderiv_continuousMultilinear_apply_const_apply hdiff (csrDirs vs) v

/-- Along a word of length `≤ k + 1`, the classical derivatives of the approximants converge
pointwise to those of the limit. -/
theorem csr_iterD_tendsto (k : ℕ) (u : ℕ → Plane → Vec)
    (hu : ∀ n, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (u n)) (G : Plane → Vec)
    (hG : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) G)
    (hGu : ∀ j : ℕ, j ≤ k + 1 →
      TendstoUniformly (fun n => iteratedFDeriv ℝ j (u n)) (iteratedFDeriv ℝ j G) atTop)
    (vs : List Plane) (hvs : vs.length ≤ k + 1) (z : Plane) :
    Tendsto (fun n => Sob.iterD vs (u n) z) atTop (𝓝 (Sob.iterD vs G z)) := by
  have e1 : Sob.iterD vs G z = iteratedFDeriv ℝ vs.length G z (csrDirs vs) :=
    congrFun (csr_iterD_eq (k + 1) G hG vs hvs) z
  have e2 : ∀ n, Sob.iterD vs (u n) z = iteratedFDeriv ℝ vs.length (u n) z (csrDirs vs) :=
    fun n => congrFun (csr_iterD_eq (k + 1) (u n) (hu n) vs hvs) z
  rw [e1]
  simp only [e2]
  exact ((continuous_eval_const (csrDirs vs)).tendsto _).comp ((hGu vs.length hvs).tendsto_at z)

/-! ### The a.e. identification of the cell derivative with the classical one -/

theorem csr_ae_deriv (c : ℝ) (hc : 0 < c) (k : ℕ) (u : ℕ → Plane → Vec)
    (hu : ∀ n, Sob.IsCylSmooth c (u n)) (G : Plane → Vec) (x : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3))
    (hlim : Tendsto (fun n => csrOf c hc k (u n) (hu n)) atTop (𝓝 x))
    (hGc : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) G)
    (hGu : ∀ j : ℕ, j ≤ k + 1 →
      TendstoUniformly (fun n => iteratedFDeriv ℝ j (u n)) (iteratedFDeriv ℝ j G) atTop)
    (β : Sob.Idx 2 (k + 1)) :
    cellDeriv c (Sob.Idx.castLE (by omega : k + 1 ≤ k + 3) β) x =ᵐ[Cyl.cellμ c]
      Sob.iterD ((Sob.cylinder c).word β) G := by
  set α : Sob.Idx 2 (k + 3) := Sob.Idx.castLE (by omega : k + 1 ≤ k + 3) β with hα
  -- each approximant: its cell derivative is its classical derivative
  have hsm : ∀ n, cellDeriv c α (csrOf c hc k (u n) (hu n)) =ᵐ[Cyl.cellμ c]
      Sob.iterD ((Sob.cylinder c).word β) (u n) := by
    intro n
    have h := Sob.W.deriv_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
      (k := k + 3) (p := 2) hc (u n) (hu n) α
    exact (csr_iso_coe c (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2
      (k + 3) 2 α (csrOf c hc k (u n) (hu n)))).trans
      (csr_ae_measure (vecH1_measure_eq_cell c) h)
  -- the cell derivatives converge in L²
  have hL : Continuous (fun y : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3) =>
      weightedToCellL2Isometry c (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ
        Cyl.Vec2 (k + 3) 2 α y)) :=
    ((weightedToCellL2Isometry c).toContinuousLinearMap.comp
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (k + 3) 2 α)).continuous
  have hH : Tendsto (fun n => weightedToCellL2Isometry c (Sob.W.deriv (Sob.cylinder c)
      (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (k + 3) 2 α (csrOf c hc k (u n) (hu n)))) atTop
      (𝓝 (weightedToCellL2Isometry c (Sob.W.deriv (Sob.cylinder c)
        (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 (k + 3) 2 α x))) :=
    (hL.tendsto x).comp hlim
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hH).exists_seq_tendsto_ae
  have hall : ∀ᵐ z ∂(Cyl.cellμ c), ∀ n,
      cellDeriv c α (csrOf c hc k (u n) (hu n)) z =
        Sob.iterD ((Sob.cylinder c).word β) (u n) z :=
    ae_all_iff.2 hsm
  have hpt : ∀ z : Plane, Tendsto (fun n => Sob.iterD ((Sob.cylinder c).word β) (u n) z) atTop
      (𝓝 (Sob.iterD ((Sob.cylinder c).word β) G z)) :=
    fun z => csr_iterD_tendsto k u (fun n => csr_cd (hu n) (k + 1)) G hGc hGu _
      (csr_word_len c β) z
  filter_upwards [hae, hall] with z hz1 hz2
  have e : (fun i => Sob.iterD ((Sob.cylinder c).word β) (u (ns i)) z) =
      (fun i => cellDeriv c α (csrOf c hc k (u (ns i)) (hu (ns i))) z) :=
    funext fun i => (hz2 (ns i)).symm
  have h1 : Tendsto (fun i => Sob.iterD ((Sob.cylinder c).word β) (u (ns i)) z) atTop
      (𝓝 (cellDeriv c α x z)) := by
    rw [e]
    exact hz1
  have h2 : Tendsto (fun i => Sob.iterD ((Sob.cylinder c).word β) (u (ns i)) z) atTop
      (𝓝 (Sob.iterD ((Sob.cylinder c).word β) G z)) :=
    (hpt z).comp hns.tendsto_atTop
  exact tendsto_nhds_unique h1 h2

/-! ### One point: the representative of a single element -/

theorem csr_exists_rep (c : ℝ) (hc : 0 < c) (k : ℕ) (C : ℝ)
    (hB : ∀ (f : Plane → Vec) (hf : Sob.IsCylSmooth c f), ∀ j : ℕ, j ≤ k + 1 → ∀ z : Plane,
      ‖iteratedFDeriv ℝ j f z‖ ≤ C * ‖csrOf c hc k f hf‖)
    (x : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3)) :
    ∃ G : Plane → Vec, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) G ∧ Cyl.IsPeriodic c G ∧
      (∀ β : Sob.Idx 2 (k + 1), cellDeriv c (Sob.Idx.castLE (by omega : k + 1 ≤ k + 3) β) x =ᵐ[Cyl.cellμ c]
        Sob.iterD ((Sob.cylinder c).word β) G) ∧
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : Plane, ‖iteratedFDeriv ℝ j G z‖ ≤ C * ‖x‖) := by
  obtain ⟨u, hu, hlim⟩ := cylSmoothDensity c hc k x
  have hlim' : Tendsto (fun n => csrOf c hc k (u n) (hu n)) atTop (𝓝 x) := hlim
  -- derivatives of differences of approximants
  have hdiffAt : ∀ (m n j : ℕ) (z : Plane),
      iteratedFDeriv ℝ j (fun z => u m z - u n z) z =
        iteratedFDeriv ℝ j (u m) z - iteratedFDeriv ℝ j (u n) z := fun m n j z =>
    iteratedFDeriv_sub_apply ((csr_cd (hu m) j).contDiffAt) ((csr_cd (hu n) j).contDiffAt)
  have hsub_bound : ∀ (m n j : ℕ), j ≤ k + 1 → ∀ z : Plane,
      dist (iteratedFDeriv ℝ j (u m) z) (iteratedFDeriv ℝ j (u n) z) ≤
        C * dist (csrOf c hc k (u m) (hu m)) (csrOf c hc k (u n) (hu n)) := by
    intro m n j hj z
    simp only [dist_eq_norm]
    rw [← hdiffAt m n j z, ← csrOf_sub c hc k (hu m) (hu n)]
    exact hB (fun z => u m z - u n z) (csr_sub (hu m) (hu n)) j hj z
  have hpt_bound : ∀ (m n : ℕ) (z : Plane),
      dist (u m z) (u n z) ≤ C * dist (csrOf c hc k (u m) (hu m)) (csrOf c hc k (u n) (hu n)) := by
    intro m n z
    have hb := hB (fun z => u m z - u n z) (csr_sub (hu m) (hu n)) 0 (Nat.zero_le _) z
    rw [norm_iteratedFDeriv_zero] at hb
    simp only [dist_eq_norm]
    rw [← csrOf_sub c hc k (hu m) (hu n)]
    exact hb
  -- uniform Cauchy property of the values and of all derivatives of order `≤ k + 1`
  have hUC0 : UniformCauchySeqOn (fun n => u n) atTop univ :=
    csr_uc_of_lip (fun n => u n) (fun n => csrOf c hc k (u n) (hu n)) C hlim'.cauchySeq univ
      (fun m n z _ => hpt_bound m n z)
  have hcau : ∀ z : Plane, CauchySeq (fun n => u n z) := fun z => hUC0.cauchySeq (mem_univ z)
  choose G hG using fun z : Plane => cauchySeq_tendsto_of_complete (hcau z)
  have hUC : ∀ j : ℕ, j ≤ k + 1 →
      UniformCauchySeqOn (fun n => iteratedFDeriv ℝ j (u n)) atTop univ := by
    intro j hj
    exact csr_uc_of_lip (fun n => iteratedFDeriv ℝ j (u n))
      (fun n => csrOf c hc k (u n) (hu n)) C hlim'.cauchySeq univ
      (fun m n z _ => hsub_bound m n j hj z)
  -- the `C^{k+1}` limit with uniform convergence of the derivatives
  have hsmooth : ∀ n, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (u n) := fun n => csr_cd (hu n) (k + 1)
  obtain ⟨hGc, hGu⟩ := contDiffLimitCauchy (k + 1) u G hsmooth hG hUC
  -- periodicity of the limit
  have hper_u : ∀ (n : ℕ) (z : Plane), u n (z.1 + c, z.2) = u n z := fun n z => by
    have e : ((z.1 + c, z.2) : Plane) = z + (c, 0) := by ext <;> simp
    rw [e, (hu n).periodic z]
  have hGper : Cyl.IsPeriodic c G := by
    intro z
    have ht : Tendsto (fun n => u n (z.1 + c, z.2)) atTop (𝓝 (G z)) := by
      simp only [hper_u]
      exact hG z
    exact tendsto_nhds_unique (hG (z.1 + c, z.2)) ht
  -- the bound passes to the limit
  have hbd : ∀ j : ℕ, j ≤ k + 1 → ∀ z : Plane, ‖iteratedFDeriv ℝ j G z‖ ≤ C * ‖x‖ := by
    intro j hj z
    have h1 : Tendsto (fun n => ‖iteratedFDeriv ℝ j (u n) z‖) atTop
        (𝓝 ‖iteratedFDeriv ℝ j G z‖) :=
      ((hGu j hj).tendsto_at z).norm
    have h2 : Tendsto (fun n => C * ‖csrOf c hc k (u n) (hu n)‖) atTop (𝓝 (C * ‖x‖)) :=
      (hlim'.norm).const_mul C
    exact le_of_tendsto_of_tendsto' h1 h2 (fun n => hB (u n) (hu n) j hj z)
  exact ⟨G, hGc, hGper, fun β => csr_ae_deriv c hc k u hu G x hlim' hGc hGu β, hbd⟩

/-! ### The Sobolev representative: linearity and assembly -/

theorem cylSobolevRep : CylSobolevRep := by
  intro c hc hc1 k
  obtain ⟨C, hC⟩ := cylSmoothSobolevBound c hc hc1 k
  choose G hG using fun x => csr_exists_rep c hc k C hC x
  have hcont : ∀ x, Continuous (G x) := fun x => (hG x).1.continuous
  have hper : ∀ x, Cyl.IsPeriodic c (G x) := fun x => (hG x).2.1
  have hadd : ∀ x y, G (x + y) = G x + G y := by
    intro x y
    refine aePeriodicEq c hc _ _ (hcont (x + y)) ((hcont x).add (hcont y)) (hper (x + y))
      (csr_per_add (hper x) (hper y)) ?_
    have e1 := (hG (x + y)).2.2.1 Sob.Idx.zero
    have e2 := (hG x).2.2.1 Sob.Idx.zero
    have e3 := (hG y).2.2.1 Sob.Idx.zero
    simp only [Sob.Idx.castLE_zero, Sob.TestDomain.word_zero, Sob.iterD_nil] at e1 e2 e3
    exact (e1.symm.trans (csr_cellDeriv_add c (Sob.Idx.zero : Sob.Idx 2 (k + 3)) x y)).trans
      (e2.add e3)
  have hsmul : ∀ (r : ℝ) (x : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3)), G (r • x) = r • G x := by
    intro r x
    refine aePeriodicEq c hc _ _ (hcont (r • x)) ((hcont x).const_smul r) (hper (r • x))
      (csr_per_smul r (hper x)) ?_
    have e1 := (hG (r • x)).2.2.1 Sob.Idx.zero
    have e2 := (hG x).2.2.1 Sob.Idx.zero
    simp only [Sob.Idx.castLE_zero, Sob.TestDomain.word_zero, Sob.iterD_nil] at e1 e2
    exact (e1.symm.trans (csr_cellDeriv_smul c (Sob.Idx.zero : Sob.Idx 2 (k + 3)) r x)).trans
      (e2.const_smul r)
  let gL : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3) →ₗ[ℝ] (Plane → Vec) :=
    { toFun := G
      map_add' := hadd
      map_smul' := fun r x => by
        rw [hsmul r x]
        rfl }
  exact ⟨gL, C, fun x => ⟨(hG x).1, (hG x).2.1⟩, fun x β => (hG x).2.2.1 β,
    fun x j hj z => (hG x).2.2.2 j hj z⟩

end UnforcedLeray.Short.PartI
