# 主張ごとの形式化状況

原論文「循環構造と収束構造の曲率的統一」（シリーズ「領域化運動論としての四色性」7/11）の主張ごとに、対応する Lean の定理と判定を示す表です。

- 対象原稿
  - 日本語版 SHA-256：dd4791bfbb5a92d980bc85bbc0083f2c78d30b8423cc2f514bb5a150e89d6711
  - 英語版 SHA-256：8c94ee95968421c7420a818e2ed7f3c7c63ef62ee72d7725e874fffdaaa2e328
- 形式化の土台：一般の Riemann 多様体。定理の適用範囲は、原稿どおり二次元・定曲率の場合に限る。
- 主張番号（C3.1〜C10.10、§11〜13）と主張の要約は、表の第1列・第2列のとおり。
- §9 の測地三角形の読み R1〜R5 は、形式化で採用した読みで、原論文全体の唯一の確定的解釈とはしない。
- 「判定の区分」から末尾までは、開発リポジトリ（非公開）のコミット cc13c18 の CLAIMS.md と同じ内容です。この見出し部分だけを公開用に改めました。表中の CI run の番号とコミットは、開発リポジトリでの検証記録を指します。

## 判定の区分

| 区分 | 意味 |
|---|---|
| 形式化済み | 主張そのものが Lean の定理になっている。sorry・独自公理・主張を置き換える仮定がなく、CI でビルド・カーネル再検査・公理報告が通った |
| 形式化済み（読みを明示） | 原稿の語の読み（形式化での定義）を行または節に明示したうえで、主張そのものが Lean の定理になっている。その読みに含まれない対象を明記する。読みは形式化で採用したもので、原論文全体の唯一の確定的解釈とはしない |
| CI 未確認 | Lean の記述はあるが、CI でまだ確認していない |
| 一部 | 主張の一部だけが形式化済み。残りの部分を明記する |
| 未着手 | Lean の対応物がまだない |
| 解釈的 | 原稿上の解釈命題。定理・定義にはしない |
| 要確認 | 形式化の前に、命題の読み方についてご確認が必要 |

## 状況表

### §3 平行線公準を収束構造として読む

| 番号 | 原稿の主張 | Lean | 状況 |
|---|---|---|---|
| C3.1 | 曲率ゼロで、法成分 Jacobi 場は j″ = 0 を満たす | `sec3_jacobi_flat`、ユークリッド平面への適用：`sec3_euclidean_plane_flat`（`hasConstSectionalCurvature_euclidean`、`riemannCurvature_euclidean`）。定義は C4.1・C4.2 の行と同じ | 形式化済み（2026-10-30、CI run #33、コミット 838e7bb）。二次元・曲率ゼロ（断面曲率 0）の Riemann 多様体で、単位速さの曲線 γ、γ に沿う平行な単位法ベクトル場 E、γ̇ に直交する Jacobi 場 J について、J = jE（j = ⟨J, E⟩）かつ j″ = 0。ユークリッド空間の標準計量では曲率テンソルが 0 であることも証明済み |
| C3.2 | j″ = 0、j(0) = 0、j′(0) = 1 ならば j(r) = r | `sec3_linear_deviation`（0 を含む開区間）、`sec3_linear_deviation_univ`（ℝ 上） | 形式化済み |
| C3.3 | 平行線公準を測地線偏差の線形性の大域的表現として読む | — | 解釈的（原稿自身が解釈的命題と明記） |
| C3.4 | 曲率ゼロの Riemann 多様体でも、大域位相が異なればユークリッド平面と同じ大域構造を持つとは限らない | `sec3_punctured_plane`（`Riemannian/PuncturedPlane.lean`） | 形式化済み（2026-10-31、CI run #47、コミット f638e71）。2026-10-31 の査読の決定（第二案「穴あき平面」）に従い、具体例 P = ℝ² \ {(0, 0)}（ユークリッド計量を制限したもの）について、完了条件の四点を証明した。(1) 二次元 Riemann 構造：P は ℝ² を模型とする C^∞ 多様体（Mathlib の開部分集合の構造）で、計量は各接空間 T_xP = ℝ² 上の ℝ² の内積。計量は滑らかで、包含写像 P → ℝ² による ℝ² の計量の引き戻しに等しい（包含写像の微分は ℝ² の恒等写像。`inner_eq_inner_mfderiv`）。(2) 曲率零：曲率テンソルが 0（`riemannCurvature_eq_zero`）、断面曲率が 0（`hasConstSectionalCurvature_zero`）。(3) 非同相性：P は ℝ² と同相でない（`not_homeomorphic`）。証明には固定版 Mathlib の既存の結果を用いた。P は ℂ \ {0} と同相で、被覆写像 exp : ℂ → ℂ \ {0}（`Complex.isAddQuotientCoveringMap_exp`）と `IsAddQuotientCoveringMap.fundamentalGroupEquiv` により、その基本群は 2πiℤ と同型なので、単連結でない。ℝ² は可縮なので単連結。(4) 測地的不完備性：t ↦ (1 − t)e₁（t < 1）は P の測地線で、有限の時刻 t = 1 で、P の点でない原点に近づく（`ray_isGeodesicFrom`、`tendsto_ray`）。初期位置 e₁・初速度 −e₁ の測地線は、どれも t < 1 でしか定義されない（`subset_Iio_of_isGeodesicFrom`。測地線の一意性、t = 1 での連続性、極限の一意性による）。したがって P は測地的に完備でない（`not_isGeodesicallyComplete`。完備性は、すべての点とすべての接ベクトルについて、その初期値の測地線が ℝ 全体で定義されること）。平坦トーラス・平坦円柱・閉測地線の一般理論は、査読の指示どおり加えていない |

### §4 Jacobi 方程式と測地線偏差関数

| 番号 | 原稿の主張 | Lean | 状況 |
|---|---|---|---|
| C4.1 | 一般の Jacobi 方程式 ∇²J + R(J, γ̇)γ̇ = 0 | `IsJacobiFieldOn`。曲率テンソル：`riemannCurvature`、`riemannCurvature_coordField`。曲線に沿う共変微分：`covAlong` | 形式化済み（2026-10-30、CI run #33、コミット 838e7bb）。一般の Riemann 多様体で、Jacobi 場を Jacobi 方程式 D_t²J + R(J, γ̇)γ̇ = 0 の解として定義する（J と D_tJ は曲線に沿って微分可能）。R は Mathlib の Levi-Civita 接続の曲率テンソル（規約 R(X, Y)Z = ∇_X∇_YZ − ∇_Y∇_XZ − ∇_[X,Y]Z）で、各点のチャートで計算し、座標ベクトル場について ∇_X∇_YZ − ∇_Y∇_XZ − ∇_[X,Y]Z に一致することを証明済み。測地線の変分の変分場がこの方程式を満たすことは C4.1 に含めず、§6 と C4.4 の幾何学的対応の後半で扱う |
| C4.2 | 2次元・定曲率 K で J = jE と書くと j″ + Kj = 0 | `sec4_jacobi_normal_eq`。定曲率：`HasConstSectionalCurvature`。平行単位法ベクトル場の存在：`exists_parallel_unit_normal` | 形式化済み（2026-10-30、CI run #33、コミット 838e7bb）。二次元・断面曲率が一定値 K の Riemann 多様体で、単位速さの曲線 γ（原稿では測地線）、γ に沿う平行な場 E（|E| = 1、E ⊥ γ̇）、γ̇ に直交する Jacobi 場 J について、J = jE（j = ⟨J, E⟩）かつ j″ + Kj = 0。導出は原稿どおり：E が平行で接続が計量と両立するので j′ = ⟨D_tJ, E⟩、j″ = ⟨D_t²J, E⟩、定曲率から ⟨R(J, γ̇)γ̇, E⟩ = Kj。このような E は、二次元の C¹ 測地線に沿って存在する（平行移動の存在と、平行移動が内積を保つことによる） |
| C4.3 | j(0) = 0、j′(0) = 1 の解が S_K（K の符号による3つの式） | `S`、`S_of_pos`・`S_of_eq_zero`・`S_of_neg`、`sec4_S_is_the_solution`（解であること、0 を含む開区間での一意性） | 形式化済み |
| C4.4 | K > 0 では開いてから閉じる方向へ、K = 0 では線形に、K < 0 では双曲的に開く | 解析的性質：`sec4_opens_then_closes`、`sec4_opens_linearly`、`sec4_opens_hyperbolically`。幾何学的対応の前半：`sec4_jacobi_eq_S`。後半：`sec6_jacobi_eq_S`（測地線による変分：`isGeodesicVariation_polarMap`、`IsGeodesicVariation.isJacobiFieldOn`） | 形式化済み（2026-10-30。後半は CI run #39、コミット 7bdf199）。S_K の読み方は確定：K > 0 では [0, π/(2√K)] で狭義増加、[π/(2√K), π/√K] で狭義減少、(0, π/√K) で正、π/√K で 0。K = 0 では S_0(r) = r。K < 0 では狭義増加で、r > 0 のとき r < S_K(r)。対応する三定理は CI 検証済み。前半（CI run #33、コミット 838e7bb）：二次元定曲率 K の Riemann 多様体で、単位速さの曲線 γ、平行な単位法ベクトル場 E、γ̇ に直交する Jacobi 場 J が J(0) = 0、D_tJ(0) = E(0) を満たせば、0 を含む開区間上で J = S_K·E、したがって ‖J‖ = |S_K|。後半：同じ多様体で、点 p から初期方向 v_θ = cos θ·e₁ + sin θ·e₂（e₁, e₂ は T_pM の正規直交基底）の測地線を並べた変分 F(r, θ) = exp_p(r·v_θ) の変分場 J(r) = ∂F/∂θ(r, θ) は、測地線 γ(r) = F(r, θ) に沿う Jacobi 場で、J ⟂ γ̇、J(0) = 0、D_rJ(0) = ν(0)（ν は ν(0) = ∂_θv_θ の平行単位法ベクトル場）を満たし、J = S_K·ν、‖J‖ = |S_K|（測地線が定義されている、0 を含む開区間上で）。逆に、γ に沿う Jacobi 場でこれらの性質をもつものはこの変分場に一致する。そのために、測地線、指数写像（定義域が開集合で、その上で滑らか）、常微分方程式の解の初期値に関する滑らかさ（`exists_contDiff_flow`）を実装した。§6 の計量表示と周長公式は、C4.4 の完了条件に含めていない。K > 0 で S_K(π/√K) = 0 となることは Jacobi 場の零点についての主張であり、測地線の大域的な再合流とは同一視しない。π/√K は、測地線と Jacobi 場がそこまで定義されている範囲で扱う |

### §5 指数表示としての収束構造

| 番号 | 原稿の主張 | Lean | 状況 |
|---|---|---|---|
| C5.1 | u = (j, j′) と置くと u′ = A_K·u | `sec5_first_order`（逆向き：`sec5_second_order_of_first_order`） | 形式化済み |
| C5.2 | A_K² = −K·I | `sec5_AK_sq` | 形式化済み |
| C5.3 | u(r) = exp(r·A_K)·u(0) | `sec5_solution_exp`、`sec5_solution_exp_of_ode` | 形式化済み（原稿どおり、r ↦ exp(r·A_K)·u(0) が解であることと解の一意性から導く） |
| C5.4 | exp(r·A_K) = C_K(r)·I + S_K(r)·A_K、C_K・S_K の級数表示 | `sec5_exp_AK`、`sec5_exp_AK_series`、`hasSum_C`、`hasSum_S`、`exp_smul_eq_of_mul_self` | 形式化済み（原稿どおり、指数級数を偶数項と奇数項に分けて導く） |

§5 の j が Jacobi 場の法成分であることは C4.2 に属します（形式化済み）。

### §6 測地極座標と距離展開

| 番号 | 原稿の主張 | Lean | 状況 |
|---|---|---|---|
| C6.1 | 点 p と、T_pM の単位ベクトル v_θ（角 θ で表示）について F(r, θ) = exp_p(r·v_θ) と置くと、(r, θ) は p の近傍における測地極座標である | `sec6_polar_coordinates`。正規近傍：`exists_normal_nbhd`（`hasFDerivAt_extChartAt_expMap_zero`）。平面の極座標：`exists_eq_norm_smul_cos_add_sin`、`smul_cos_add_sin_inj` | 形式化済み（2026-10-30、CI run #40、コミット ed51c1c）。二次元・定曲率 K の Riemann 多様体で、e₁, e₂ を T_pM の正規直交基底、v_θ = cos θ·e₁ + sin θ·e₂ とする。ある ε₀ > 0 があって、0 < ε ≤ ε₀ のとき、B_ε = {v ∈ T_pM : ‖v‖ < ε}、U = exp_p(B_ε) について次が成り立つ。U は p の開近傍で、exp_p : B_ε → U は微分同相（B_ε は exp_p の定義域に含まれ、exp_p は B_ε 上で滑らかかつ単射で、U 上で滑らかな逆写像をもつ）。F はその定義域で滑らかで、F(0, θ) = p。0 < r < ε のとき F(r, θ) は U∖{p} の点で、U∖{p} のすべての点はこの形に書ける。0 < r, r′ < ε のとき F(r, θ) = F(r′, θ′) ⟺ r = r′ かつ θ′ − θ ∈ 2πℤ。0 < r < ε のとき ∂F/∂r, ∂F/∂θ は F(r, θ) の接空間の基底。exp_p の逆写像は、exp_p の 0 での微分が恒等写像であることから、Mathlib の逆関数定理を p のチャートで用いて構成する。定曲率は最後の基底の主張（‖∂F/∂θ‖ = |S_K(r)| > 0）にだけ使い、そのため K > 0 では ε₀ ≤ π/√K とした |
| C6.2 | 放射方向について ⟨∂F/∂r, ∂F/∂r⟩ = 1 | `norm_pR_polarMap` | 形式化済み（2026-10-30、CI run #39、コミット 7bdf199）。一般の Riemann 多様体で、v_θ が単位ベクトルなら F の定義域全体で ‖∂F/∂r‖ = 1（r ↦ F(r, θ) は初速 v_θ の測地線で、平行移動は長さを保つ） |
| C6.3 | Gauss の補題 ⟨∂F/∂r, ∂F/∂θ⟩ = 0。したがって計量は ds² = dr² + f(r)²·dθ² の形 | `inner_pR_pθ_polarMap`、`sec6_metric_form` | 形式化済み（2026-10-30。Gauss の補題は CI run #39、コミット 7bdf199。計量の形は CI run #41、コミット 11c959b）。一般の Riemann 多様体で、すべての θ について v_θ が単位ベクトルなら、F の定義域全体で ⟨∂F/∂r, ∂F/∂θ⟩ = 0。証明は ∂_r⟨∂_rF, ∂_θF⟩ = ⟨∂_rF, D_θ∂_rF⟩ = ½·∂_θ‖∂_rF‖² = 0（対称補題 D_r∂_θF = D_θ∂_rF と測地線の方程式による）と、r = 0 での値 0 から。計量の形：定義域内の微分可能な曲線 t ↦ (r(t), θ(t)) の像の速さの二乗は r′² + f²·θ′²、f = ‖∂F/∂θ‖。二次元・定曲率では f = |S_K(r)| で、r だけで決まる（C6.4、C6.5） |
| C6.4 | 角方向の変分場 J(r) = ∂F/∂θ(r, θ) は測地線に沿う Jacobi 場で、前節より |J(r)| = S_K(r) | `isJacobiFieldOn_polarMap`（一般の変分：`IsGeodesicVariation.isJacobiFieldOn`）、`sec6_jacobi_eq_S`、`norm_pθ_polarMap`、`norm_pθ_polarMap_eq_S` | 形式化済み（2026-10-30。CI run #39、コミット 7bdf199。‖J‖ = S_K の形は CI run #41、コミット 11c959b）。前半は一般の Riemann 多様体で証明：測地線による変分の変分場は Jacobi 方程式を満たす。変分の対称補題と、曲率の恒等式 D_rD_θ∂_rF − D_θD_r∂_rF = R(∂_rF, ∂_θF)∂_rF から導く（C4.1 の、Jacobi 方程式の解としての定義とは別に、変分からの導出として証明している）。後半は二次元・定曲率 K で：J ⟂ γ̇、J(0) = 0、D_rJ(0) = ∂_θv_θ であり、前節の結果（C4.4 の前半、`sec4_jacobi_eq_S`）から J = S_K·ν（ν は平行単位法ベクトル場）、‖J‖ = |S_K(r)|。r ≥ 0（K > 0 では r ≤ π/√K も）では ‖J‖ = S_K(r) |
| C6.5 | 測地極座標における計量は ds² = dr² + S_K(r)²·dθ² | `sec6_metric` | 形式化済み（2026-10-30、CI run #39、コミット 7bdf199。CI run #41 で C6.3 の計量の形を経由する証明に整理）。二次元・定曲率 K で、F の定義域内の微分可能な曲線 t ↦ (r(t), θ(t)) について、像曲線の速さの二乗は r′² + S_K(r)²·θ′² |
| C6.6 | 半径 r の測地円の周方向の長さ要素は S_K(r)·dθ、周長は 2π·S_K(r) | `sec6_circumference`、`sec6_circumference_eq_S`（長さ要素：`norm_pθ_polarMap_eq_S`） | 形式化済み（2026-10-30。CI run #39、コミット 7bdf199。2π·S_K の形は CI run #41、コミット 11c959b）。二次元・定曲率 K で、測地円 θ ↦ F(r, θ)（すべての θ で定義されているもの）の 0 ≤ θ ≤ 2π での長さ（Mathlib の `Manifold.pathELength`）は 2π·|S_K(r)|。r ≥ 0（K > 0 では r ≤ π/√K も）では 2π·S_K(r)。0 < r < ε（C6.1 の ε）では、この曲線は 0 ≤ θ < 2π で単射（C6.1） |

§6 の主張番号 C6.1〜C6.6 は、検証報告の主張一覧では一行にまとめられているため、原稿 §6 の主張を記述順に割り当てた。

### §7 角度循環とオイラー公式

| 番号 | 原稿の主張 | Lean | 状況 |
|---|---|---|---|
| C7.1 | 各接空間に、計量と向きに適合する90°回転 J があり、J² = −I | 内積空間：`Jrot`、`sec7_J_metric`、`sec7_J_orientation`、`sec7_J_sq`。Riemann 多様体の接空間：`sec7_tangent_J_metric`、`sec7_tangent_J_orientation`、`sec7_tangent_J_sq` | 形式化済み（接空間への適用は 2026-10-28 追加、CI run #16 で確認）。Mathlib には多様体の向きの概念がないため、各接空間の**任意の**向きについて述べる（多様体の向きが与える向きはその特別な場合）。計量や多様体の滑らかさは使わないので、Mathlib の C^∞ Riemann 多様体はその特別な場合 |
| C7.2 | 角 θ の回転は exp(θJ)、exp(θJ) = cos θ·I + sin θ·J | 内積空間：`sec7_exp_J`、`sec7_rotation_eq_exp`。接空間：`sec7_tangent_exp_J`、`sec7_tangent_rotation_eq_exp` | 形式化済み（注は C7.1 と同じ） |
| C7.3 | ユークリッド平面では平行移動で接空間を大域的に同一視でき、J は i の乗法に対応する | 平行移動：`sec7_euclidean_plane_parallelTransport`（一般のユークリッド空間：`euclidean_parallelTransport`）。その基礎：`covAlong`、`IsParallelAlongOn`、`isLeviCivitaConnection_trivialCov`、`covAlong_euclidean`、`euclidean_isParallelAlongOn_iff`。J と i：`sec7_euclidean_plane_tangent_J`（各接空間の J）、`sec7_euclidean_plane_J`、`sec7_J_corresponds_to_I`、`sec7_exists_complex_identification`、`sec7_J_complex` | 形式化済み（2026-10-30、CI run #31、コミット 6890223）。曲線は開区間上で微分可能なもの。「平行」は、Mathlib の標準計量の Levi-Civita 接続について、曲線に沿う共変微分が 0 であること。どの曲線に沿っても平行移動は T_xℝ² = ℝ² の同一視のもとで恒等写像であり、同一視は曲線によらない。ℝ² の向き o をこの同一視で各接空間へ移すと、向きを保つ一つの線形等長写像 φ : ℝ² ≃ ℂ のもとで、すべての接空間の J（その点の Riemann 計量と向きから作る C7.1 の J）が i の乗法になる |
| C7.4 | e^{iθ} = cos θ + i·sin θ | `sec7_euler`、`sec7_exp_J_complex` | 形式化済み（原稿どおり、exp(θJ) = cos θ·I + sin θ·J から J を i の乗法と同一視して導く） |

### §8 循環構造と収束構造

| 番号 | 原稿の主張 | Lean | 状況 |
|---|---|---|---|
| C8.1 | 二つの指数構造の対比と統一 | — | 解釈的。数学的部分（二つの指数表示）は C5.4 と C7.2 で、どちらも同一の定理 `exp_smul_eq_of_mul_self`（A² = −K·I ならば exp(rA) = C_K(r)·I + S_K(r)·A）の適用として形式化済み |

### §9 定曲率正弦定理

| 番号 | 原稿の主張 | Lean | 状況 |
|---|---|---|---|
| C9.1 | 測地三角形について sin A / S_K(a) = sin B / S_K(b) = sin C / S_K(c) | 模型空間：`HypPlane.sine_law`、`SphereModel.sine_law`。技術的条件の下（一般の二次元定曲率 Riemann 多様体）：`GeodesicTriangle.sine_law` | 形式化済み（読みを明示、2026-11-01）。§9 の読み R1〜R4 の下で、K < 0 では非退化のすべての測地三角形について、K > 0 では三辺が開半球に含まれ 0 < a, b, c < π/√K の非退化測地三角形について、正弦定理が成り立つ。技術的条件は仮定せず、模型空間で証明している（C9.3 の行）。導出は原稿どおり、三つの余弦定理（C9.3）から C9.5〜C9.7 を経る。K = 0 は原稿どおり C9.8 の極限で扱う。模型空間でない定曲率曲面では、技術的条件 `SidesInNormalBalls` の下の定理として残る（§9 の節）。技術的条件は「各頂点について、その頂点を中心とする正規球（指数写像が微分同相になる接空間の球の像）が三辺を含む」こと |
| C9.2 | K > 0、0 < a, b, c < π/√K ならば S_K(a), S_K(b), S_K(c) > 0 | `S_pos`（K ≤ 0 の場合：`S_pos_of_nonpos`） | 形式化済み |
| C9.3 | 定曲率余弦定理 | 模型空間（K ≠ 0。原稿の C9.3 に対応）：`HypPlane.cosine_law`、`SphereModel.cosine_law`。K = 0 への特殊化（両辺とも 1 に退化）：`EuclideanPlane.cosine_law`。技術的条件の下：`GeodesicTriangle.cosine_law`（各頂点：`cosine_law_segments`）。模型空間で技術的条件を示す段：`EuclideanPlane.sidesInNormalBalls`、`HypPlane.sidesInNormalBalls`、`SphereModel.sidesInNormalBalls_of_inOpenHemisphere`、`isNormalBall_of_constCurvature`。正規球内：`cosine_law_normalBall'`（`cosine_law_normalBall`、`cosine_law_normalBall_of_mem`）。測地極座標での計算：`hasDerivAt_S_mul_polar`、`S_smul_covθ_pR_polarMap`。K = 0 を含むすべての K で成り立つ形（G_K による形、2026-11-01 追加）：`GeodesicTriangle.cosine_law_G`（正規球内：`cosine_law_normalBall_G'`）、ℝ² の測地三角形での K = 0 の形：`EuclideanPlane.cosine_law_G`、`EuclideanPlane.cosine_law_zero` | 形式化済み（読みを明示、2026-11-01）。§9 の読み R1〜R3 の下で、K ≤ 0 ではすべての測地三角形、K > 0 では三辺が開半球に含まれる測地三角形について、三つの頂点それぞれで C_K(c) = C_K(a)C_K(b) + K·S_K(a)S_K(b)·cos C が成り立つ。**K = 0 との対応（2026-11-01 の査読による照合）**：原稿の C9.3 は、§9 の K ≠ 0 の場合の導出の中で述べられている（日本語版 §9「以下では、まず K ≠ 0 の場合を扱う」に続く「まず、定曲率幾何の余弦定理は…」。英語版 §9 "We first treat the case K ≠ 0" に続く "First, the constant-curvature law of cosines is …"）。K = 0 は C9.8 の連続極限で扱われる（「K = 0 の場合は、上の導出が分母に K を含むため、直接には適用できない。そこで連続極限によって扱う」）。原稿は通常のユークリッド余弦定理 a² = b² + c² − 2bc·cos A を主張していない。したがって C9.3 に対応する Lean の定理は、K ≠ 0 の `HypPlane.cosine_law`・`SphereModel.cosine_law`（技術的条件の下では `GeodesicTriangle.cosine_law`）である。`EuclideanPlane.cosine_law` は一般化公式の K = 0 への特殊化で、C_0 = 1 のため両辺とも 1 に退化し、ユークリッド余弦定理を表さない。原稿の主張に対応する定理としては数えない（定理そのものは保存）。K = 0 での非自明な関係は C9.8 の段にある。余弦定理で定める cos A_K を K = 0 まで連続に延ばした値が (b² + c² − a²)/(2bc) であること（`cosLaw_zero`、級数 G_K による代数的計算）と、この A_0 をユークリッドの三角形の角と同定する段（`angleK_zero_eq_angle`、Mathlib のユークリッド余弦定理 `law_cos` を用いる。C10.10 の行に記録済みの依存）である。**追加（2026-11-01、CI run #55）**：下の (1) と同じ議論（測地極座標で g = G_K(r∘σ) が g″ + Kg = 1 を満たすこと。G_K′ = S_K、C_K = 1 − K·G_K による）で、G_K(c) = G_K(a) + G_K(b) − K·G_K(a)G_K(b) − S_K(a)S_K(b)·cos C を、K = 0 を含むすべての K について証明した（`GeodesicTriangle.cosine_law_G`）。K ≠ 0 では原稿の式と同値（両辺を 1 から引いて K で割る）で、K = 0 では c²/2 = a²/2 + b²/2 − ab·cos C になる。原稿はこの K = 0 の形を主張として述べていないので、C9.3 に対応する定理の範囲は上のとおりで変えない。この形は、C9.8 で A_0 をユークリッドの角と同定する段を `law_cos` を用いずに行うために用いる（C9.8 の行、§9 の読み R5）。証明は二段。(1) 正規球内の余弦定理：二次元・定曲率 K の Riemann 多様体で、点 p を中心とする正規球 exp_p(B_ρ) に含まれる単位速さの測地線分 σ が、p からの単位速さの測地線 γ 上の点 γ(a) から点 exp_p(c·w)（‖w‖ = 1）へ向かうとき、C_K(c) = C_K(a)C_K(b) + K·S_K(a)S_K(b)·cos C（σ が p を通る退化の場合も含む）。測地極座標で h = C_K(r∘σ) が h″ + Kh = 0 を満たすこと（S_K·D_θ∂_rF = C_K·∂_θF と Gauss の補題による）と、初期値問題の一意性による。これを技術的条件 `SidesInNormalBalls` の下で三頂点に適用する（`GeodesicTriangle.cosine_law`）。(2) 模型空間では技術的条件を証明する（仮定に加えない）。二次元・定曲率で exp_p の微分が可逆であること（K > 0 では半径 π/√K まで）から、exp_p が単射な球は正規球になる（`isNormalBall_of_constCurvature`）。ユークリッド平面・双曲平面では exp_p が接平面全体から全単射で、すべての球が正規球（`EuclideanPlane.isNormalBall`、`HypPlane.isNormalBall`）。球面では半径 π/√K の球が正規球で、その像は対蹠点以外の全体（`SphereModel.isNormalBall`、`SphereModel.mem_expMap_image_of_ne`）。K > 0 の辺長条件だけでは一般の定曲率多様体で切断点を避けられない（例：曲率 1 の実射影平面では切断距離が π/2）。そのため、模型空間でない定曲率曲面では辺長条件で技術的条件を置き換えない |
| C9.4 | C_K = S_K′、C_K² + K·S_K² = 1 | `hasDerivAt_S`、`C_sq_add_mul_S_sq` | 形式化済み |
| C9.5 | 余弦定理から cos A = (X − YZ)/(KQR)、sin²A / P² = (1 − X² − Y² − Z² + 2XYZ)/(K²P²Q²R²) | `sec9_sin_sq_div_eq` | 形式化済み。余弦定理は、原稿の導出と同じくこの段の前提として入る（余弦定理そのものは C9.3 の行）。C_K² + K·S_K² = 1 は仮定せず証明している |
| C9.6 | 右辺の対称性から sin²A / P² = sin²B / Q² = sin²C / R² | `sec9_sin_sq_ratios_eq` | 形式化済み（前提は C9.5 と同じ） |
| C9.7 | 非退化測地三角形では 0 < A, B, C < π、平方根をとって正弦定理 | 平方根をとる段：`sec9_sine_law_of_cos_law`。角：`EuclideanPlane.angle_pos_lt_pi`、`HypPlane.angle_pos_lt_pi`、`SphereModel.angle_pos_lt_pi`（技術的条件の下：`GeodesicTriangle.angle_pos_lt_pi`、各頂点：`angle_pos_lt_pi_segments`） | 形式化済み（読みを明示、2026-11-01）。平方根をとる段は形式化済み。§9 の読み R1〜R3 の下で、非退化（どの頂点も対辺上にない）の測地三角形の角は (0, π) にある（K ≤ 0 はすべての三角形、K > 0 は三辺が開半球に含まれる三角形）。角が 0 なら、一辺がもう一辺を逆にたどった線分と重なり、どちらかの頂点が対辺上にのる。π なら、二辺をつないだ測地線と第三の辺が正規球の中で一致し、頂点が対辺上にのる。どちらも非退化の仮定に反する。K = 0（ユークリッドの三角形）では、非共線から角が (0, π) にあることも証明済み |
| C9.8 | K → 0 の極限でユークリッド正弦定理 | `sec9_model_triangles`、`HypPlane.exists_triangle`、`SphereModel.exists_triangle`、`HypPlane.angles_eq_angleK`、`SphereModel.angles_eq_angleK`、`sec9_limit`、`tendsto_S_zero`、`angleK_zero_eq_angle`、`sec9_euclidean_sine_law`（技術的条件の下：`GeodesicTriangle.angles_eq_angleK`）。Riemann 層を経る導出（2026-11-01 追加）：`CurvatureChain.hyperbolic_sine_law`、`CurvatureChain.sine_law_limit`、`EuclideanPlane.angle_eq_angleK_zero`（`GeodesicTriangle.angles_eq_angleK_zero`）、`CurvatureChain.euclidean_sine_law` | 形式化済み（読みを明示、2026-11-01）。非退化三角形の辺長 a, b, c を固定する。0 に近い各 K < 0 で双曲平面に、0 に近い各 K > 0 で球面に（開半球の中に）、辺長 a, b, c の測地三角形が存在する（原稿の「曲率 K に応じて定まる測地三角形」。頂点 A に角 A_K = `angleK K a b c` をとって構成し、第三辺の長さが a であることを、双曲平面では Lorentz 内積、球面では ℝ³ の内積で示す）。その角は余弦定理で定まる A_K, B_K, C_K に等しい。A_K, B_K, C_K は K について連続で A_0, B_0, C_0 に収束し、S_K(x) → x、正弦定理が極限へ移る。A_0, B_0, C_0 は辺長 a, b, c のユークリッドの三角形の角（`angleK_zero_eq_angle`）で、結論 sin A_0 / a = sin B_0 / b = sin C_0 / c を得る（ユークリッドの三角形の角についての正弦定理 `sec9_euclidean_sine_law`）。三角形の存在は、極限の議論に必要な 0 の近くの K について示した（K < 0 では cos A_K ∈ (−1, 1) のとき、K > 0 では加えて √K·a、√K·b、√K·c < π/2 のとき）。**Riemann 層を経る導出（2026-11-01、CI run #55）**：0 に近い各 K < 0 について、双曲平面の辺長 a, b, c の測地三角形が満たす正弦定理を、その三角形の余弦定理（C9.3）から C9.5〜C9.7 で導き、その角が A_K, B_K, C_K であることと合わせて、K → 0⁻ の極限へ移した（`CurvatureChain.hyperbolic_sine_law`、`CurvatureChain.sine_law_limit`。K = 0 で連続な関数の極限なので片側の極限で足りる）。A_0, B_0, C_0 をユークリッドの角と同定する段は、ℝ² の三角形を曲率 0 の模型の測地三角形として扱い、K = 0 を含む形の余弦定理（C9.3 の行の追加分）で行った（`EuclideanPlane.angle_eq_angleK_zero`。`law_cos` を用いない。§9 の読み R5）。結論は ℝ² のユークリッド正弦定理 `CurvatureChain.euclidean_sine_law`。従来の `sec9_limit`・`angleK_zero_eq_angle`・`sec9_euclidean_sine_law`（一般のユークリッド空間）は変更せず保存する |

**§9 の測地三角形の読み（原稿との区別、2026-11-01）**　C9.1・C9.3・C9.7・C9.8 に共通。

- R1（対象）：原稿の「定曲率 K の二次元幾何」を、曲率 K の模型空間と読む。K = 0 はユークリッド平面 ℝ²（`EuclideanPlane`）。K < 0 は双曲平面 `hypPlane K`（双曲面 y₀² + K‖y‖² = 1 の上の葉を座標 y = x で表した計量 g_x(a, b) = ⟨a, b⟩ + K⟨x, a⟩⟨x, b⟩/(1 − K‖x‖²)）。K > 0 は単位球面に (1/K)×標準計量を入れた `SphereModel.sph K`（半径 1/√K の球面と等長。Mathlib の立体射影のチャートによる多様体構造）。いずれも、これまでと同じ一般の Riemann 多様体の枠組み（Mathlib の多様体と `RiemannianBundle`）で構成し、曲率が K であることを証明している（`hasConstSectionalCurvature_euclidean`、`HypPlane.hasConstSectionalCurvature`、`SphereModel.hasConstSectionalCurvature`）。
- R2（凸性）：K ≤ 0 では凸性の仮定は要らない。すべての測地三角形が技術的条件を満たす（`EuclideanPlane.sidesInNormalBalls`、`HypPlane.sidesInNormalBalls`）。K > 0 では、原稿の「凸測地三角形」を「三辺が開半球に含まれる」（`SphereModel.InOpenHemisphere`）と読む。このとき技術的条件が従う（`SphereModel.sidesInNormalBalls_of_inOpenHemisphere`）。
- R3（測地三角形・非退化）：測地三角形は `GeodesicTriangle`（三頂点と三本の選択された単位速さの測地線分。辺長は選択された線分の長さ、頂点角はその頂点から出る二辺の初速度のなす角）、非退化は `GeodesicTriangle.Nondegenerate`（どの頂点も対辺上にない）。
- R4（辺長条件）：K > 0 の 0 < a, b, c < π/√K は、原稿どおり別の仮定として保つ（正弦定理と A_K の同定で用いる）。技術的条件 `SidesInNormalBalls` と原稿の凸測地三角形とは同一視しない（2026-11-01 の査読）。
- R5（K = 0 の角の同定、C9.8、2026-11-01 追加）：原稿は C9.8 で A_0, B_0, C_0 をユークリッドの三角形の角とする方法を書いていない。形式化には二通りがある。(i) `angleK_zero_eq_angle`：Mathlib のユークリッド余弦定理 `law_cos` による（従来。一般のユークリッド空間）。(ii) `EuclideanPlane.angle_eq_angleK_zero`：ℝ² を曲率 0 の模型とし、その測地三角形について K = 0 を含む形の余弦定理（G_K による形。K ≠ 0 では原稿の余弦定理と同値）から同定する。(ii) は、原稿の「定曲率余弦定理により、これらの角度は K に連続的に依存し」の余弦定理を K = 0 まで含めて読んだもので、§12 の連鎖（`CurvatureChain`）は (ii) を用いる。
- 含まない対象：模型空間でない定曲率曲面（穴あき平面、平坦トーラス、実射影平面など）の三角形。そこでは C9.1・C9.3・C9.7・C9.8 を、技術的条件 `SidesInNormalBalls` の下の定理（`GeodesicTriangle.*`）としてだけ形式化している。穴あき平面の凸三角形 A = (1, 0)、B = (2, 0)、C = (1, 2) は技術的条件を満たさない（2026-11-01 の査読）ので、一般の定曲率曲面では凸性から技術的条件は従わない。K > 0 で三辺が開半球に含まれない球面三角形も含まない。

### §10 Jackson–Johnson 第2証明

| 番号 | 原稿の主張 | Lean | 状況 |
|---|---|---|---|
| C10.1 | 直角三角形の設定：α + β = 90°、a < b ⟺ α < 45° < β | `sec10_setting` | 形式化済み |
| C10.2 | 点 D の構成：∠BAX は 0 から β へ連続に狭義増加し、∠BAD = α となる D が B 側の延長上にただ一つある | `sec10_angle_increases`、`sec10_exists_unique_D` | 形式化済み（原稿どおり、連続性・単調性と中間値の定理による） |
| C10.3 | BD = CD − a | `sec10_BD_eq` | 形式化済み |
| C10.4 | ∠CAD = 2α、∠ACD = 90°、∠ADC = ∠ADB = β − α | `sec10_angles` | 形式化済み |
| C10.5 | 三角形 ACD と ABD での正弦定理 | `sec10_sine_laws`。§12 の連鎖を経る版（ℝ²）：`CurvatureChain.sec10_sine_laws` | 形式化済み。用いる正弦定理は、§9 の K → 0 極限として得た `sec9_euclidean_sine_law`。§12 の連鎖を経る版（2026-11-01、CI run #55）では、Riemann 層を経て得た ℝ² の正弦定理 `CurvatureChain.euclidean_sine_law`（C9.8 の行）を用いる |
| C10.6 | sin α = a/c、cos α = b/c、sin β = b/c、cos β = a/c | `sec10_right_ratios`。§12 の連鎖を経る版（ℝ²）：`CurvatureChain.sec10_right_ratios` | 形式化済み。比は仮定せず、正弦定理（sin 90° = 1）と角の和から導く |
| C10.7 | sin 2α = 2ab/c²、sin(β − α) = (b² − a²)/c² | `sec10_double_and_difference` | 形式化済み |
| C10.8 | CD = 2ab²/(b² − a²)、BD = a(a² + b²)/(b² − a²)、BD = ac²/(b² − a²) | `sec10_two_expressions`。§12 の連鎖を経る版（ℝ²）：`CurvatureChain.sec10_two_expressions` | 形式化済み |
| C10.9 | a² + b² = c² | `sec10_pythagoras`。§12 の連鎖を経る版（ℝ²）：`CurvatureChain.sec10_pythagoras` | 形式化済み。仮定は直角（∠ACB = 90°、A ≠ C、B ≠ C）と a < b だけ。§12 の連鎖を経る版（2026-11-01、CI run #55）：§10 の証明を、正弦定理を仮定とした形 `sec10_*_of_sineLaw`（`Sec10OfSineLaw.lean`。`Sec10.lean` の証明の写しで、`sec9_euclidean_sine_law` を仮定に置き換えたもの。C10.1〜C10.9 のすべてにある）にし、そこへ Riemann 層を経る ℝ² の正弦定理を与えた（`CurvatureChain.sec10_pythagoras`）。対象は ℝ²（原稿の「ユークリッド平面」）。従来の `sec10_pythagoras`（一般のユークリッド空間）は変更せず保存する |
| C10.10 | 本証明の性格（用いるのは正弦定理・二倍角公式・差の公式・有限の代数のみ） | 点検：`scripts/DependencyReport.lean` | メタ主張。形式証明の依存関係で点検済み（2026-10-31）。2026-10-31 の査読の判定に従い、原稿の「のみ」は有限の三角法的計算の段について述べたものとして扱い、証明木全体についての排他的な独立性の主張としては扱わない。(a) 有限の三角法的計算の段（C10.5〜C10.9）：正弦定理は `sec10_sine_laws`（§9 の `sec9_euclidean_sine_law`）。三角関数の公式として直接用いるのは、二倍角公式 `Real.sin_two_mul` と差の公式 `Real.sin_sub`（C10.7）、C10.6 `sec10_right_ratios` の sin 90° = 1（`Real.sin_pi_div_two`）と sin(π/2 − x) = cos x（`Real.sin_pi_div_two_sub`）。(b) 証明木全体：C10.9 `sec10_pythagoras` が依存する宣言を、コンパイル済みの環境から機械的に列挙した（直接・推移的に 57 個。すべて `SK`・`Sec09`・`Sec10` のもので、Riemann 層の宣言は含まない）。原稿 C10.1〜C10.4 の作図と角の段では、三角形の内角の和 `angle_add_angle_add_angle_eq_pi`、角の加法性、角の連続性と中間値の定理（点 D の構成）と、正弦の正値性・単調性・下からの評価（`Real.sin_pos_of_pos_of_lt_pi`、`Real.strictMonoOn_sin`、`Real.mul_le_sin`）を用いる。正弦定理の側では、§9 の導出（C9.4・C9.5）どおり sin² + cos² = 1 を用いる。K = 0 の角 A_0 をユークリッドの角と同定する段 `angleK_zero_eq_angle` は、一般のユークリッド余弦定理 `law_cos p₂ p₁ p₃`（Mathlib）を用いる。この段から `sec9_euclidean_sine_law` を経由して `sec10_pythagoras` に至る使用経路がある。査読の判定に従い、これを三平方的距離構造への基礎づけ上の依存として記録する（Lean カーネル内に形式的な循環証明があるということではない）。旧記載の訂正：sin(π/2 − x) = cos x を C10.1〜C10.4 の段に含めていたのは誤りで、C10.6 の段に移した。正弦の正値性・単調性・下からの評価は旧記載から漏れていた。**§12 の連鎖を経る版の点検（2026-11-01、CI run #55）**：`CurvatureChain.sec10_pythagoras`（ℝ²）について、Mathlib を含む依存関係の全体を機械的に点検した（`scripts/DependencyReport.lean` の `#dependency_check_full`。`#dependency_require_full` は違反があれば失敗し、CI の Dependency report の段で毎回実行される）。`law_cos`（距離の形 `dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`、ベクトルと角の形 `norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle` を含む）と、Mathlib の三平方の定理（ベクトルの形 `norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero` など。角の形はその Mathlib のモジュール自体を読み込んでいない）は、どこにも現れない。`angleK_zero_eq_angle`・`sec9_euclidean_sine_law` も用いない。用いるのは、Jacobi 方程式（`sec4_jacobi_eq_S`、`sec6_jacobi_eq_S`）、測地極座標の計算（`hasDerivAt_S_mul_polar`）、双曲平面の辺長 a, b, c の測地三角形（`HypPlane.exists_triangle`、`HypPlane.cosine_law`）、K = 0 を含む形の余弦定理（`GeodesicTriangle.cosine_law_G`）、平坦な模型での同定（`EuclideanPlane.angle_eq_angleK_zero`）である。内積への依存は残り、接空間の水準へ移る。とくに、接平面での三平方の関係を用いる。正規直交な組 w₁, w₂ についての ‖x‖² = ⟨w₁, x⟩² + ⟨w₂, x⟩²（`norm_sq_eq_inner_sq_add_inner_sq`。測地極座標の持ち上げ `exists_polar_lift` で使用）と、測地極座標での速度の分解 |σ′|² = r′² + S_K(r)²·θ′²（`sec6_metric`。`hasDerivAt_S_mul_polar` で使用）である。ほかに Mathlib の正規直交基底と極化恒等式を用いる。双曲平面の模型の計算は座標平面の内積の展開 ‖x − y‖² = ‖x‖² − 2⟨x, y⟩ + ‖y‖²（`norm_sub_sq_real`、`HypPlane.K_mul_gH_sub` で使用）と ‖x + y‖² の展開（`norm_add_sq_real`、`HypPlane.fderiv_gH` で使用）を用いる。§10 の段は、原稿どおり Mathlib の三角形の内角の和 `angle_add_angle_add_angle_eq_pi` を用いる（その Mathlib の証明は `law_cos` も上の展開も用いない）。これは原稿 §11 の「三平方的距離構造への依存は、ユークリッド平面全体から接空間計量と曲率構造へ移される」に沿った記録で、三平方的構造からの独立は主張しない。従来の `sec10_pythagoras` の `law_cos` への依存の記録は、その定理についてそのまま有効 |

§10 の定理は、ユークリッド平面に限らず任意のユークリッド空間（実内積空間上のアフィン空間）で成り立つ形で証明しています。原稿の平面の場合はその特別な場合です。

### §11〜13 結論部

| 番号 | 原稿の主張 | Lean | 状況 |
|---|---|---|---|
| §11〜13 | 循環性の所在、標準文献との関係、結論 | — | 解釈的。§12 の連鎖（Jacobi 場 ⇒ S_K ⇒ 定曲率正弦定理 ⇒ K = 0 ⇒ 三平方定理の三角法的証明）について、2026-10-31 の査読の判定に従い、次のとおり記録する。（2026-10-31 時点）連鎖は、一つの Lean の証明の依存関係としては実現されていない。また、`sec10_pythagoras` が Riemann 層に依存しないことだけを理由に、§12 に欠陥があるとは判定しない。各段の状況：「Jacobi 場 ⇒ S_K」は C4.4・C6.4 で形式化済み。「定曲率正弦定理」の測地三角形の部分（C9.1、C9.3、C9.7、C9.8）は、§9 の読み R1〜R4 を明示したうえで模型空間で形式化済み（模型空間でない定曲率曲面では技術的条件の下）。連鎖の形式的な依存関係（2026-10-31 点検、`scripts/DependencyReport.lean`）：`GeodesicTriangle.sine_law`（K ≠ 0、技術的条件の下）は、測地線による変分の変分場が Jacobi 場であること（`IsGeodesicVariation.isJacobiFieldOn`）、Jacobi 場 = S_K·ν（`sec4_jacobi_eq_S`、`sec6_jacobi_eq_S`）、測地極座標での計算、正規球内の余弦定理に依存する。一方、C10.9 の証明 `sec10_pythagoras` は Riemann 層のどの宣言にも依存しない。そこで用いる K → 0 の段 `sec9_euclidean_sine_law` は、余弦定理で定める角 A_K についての代数的な正弦定理と、その極限による。A_0 をユークリッドの角と同定する段では、ユークリッド余弦定理 `law_cos` を用いる。Riemann 層との接続は、K ≠ 0 で A_K が実際の測地三角形の角に等しいこと（`GeodesicTriangle.angles_eq_angleK`）と、模型空間に辺長 a, b, c の測地三角形が存在すること（`sec9_model_triangles`）による。`law_cos` を用いる段から `sec10_pythagoras` に至る使用経路の評価は C10.10 の行に記す。**連鎖の実現（2026-11-01、CI run #55）**：`CurvatureChain.sec10_pythagoras`（ℝ²）の証明は、Jacobi 場 ⇒ S_K（`sec4_jacobi_eq_S`、`sec6_jacobi_eq_S`）⇒ 測地三角形の余弦定理 ⇒ K < 0 の測地三角形の正弦定理（`CurvatureChain.hyperbolic_sine_law`）⇒ K → 0（`CurvatureChain.sine_law_limit`、A_0 の同定は平坦な模型の余弦定理 `EuclideanPlane.angle_eq_angleK_zero`）⇒ ユークリッド正弦定理（`CurvatureChain.euclidean_sine_law`）⇒ §10（`sec10_pythagoras_of_sineLaw`）という、一つの形式的な依存関係を持つ（C10.10 の行の点検）。§11〜13 そのものは解釈的な主張のまま、定理にはしない |

## 集計（2026-11-01 改訂時点）

| 区分 | 項目 |
|---|---|
| 形式化済み | C3.1、C3.2、C3.4、C4.1〜C4.4、C5.1〜C5.4、C6.1〜C6.6、C7.1〜C7.4、C9.2、C9.4〜C9.6、C10.1〜C10.9 |
| 形式化済み（読みを明示） | C9.1、C9.3、C9.7、C9.8（模型空間で、§9 の読み R1〜R4 の下。C9.8 の Riemann 層を経る導出は加えて R5 の下。模型空間でない定曲率曲面では技術的条件の下） |
| 一部 | なし |
| 要確認 | なし。§9 の読み R1〜R4（対象・凸性・測地三角形と非退化の定義・辺長条件の扱い）は、模型空間版の形式化で採用した読みとして保持する。R5（C9.8 の A_0 の同定。2026-11-01 追加）も形式化で採用した読みとして記録し、確定的解釈とはしない。原論文全体の唯一の確定的解釈へは昇格させない（2026-11-01 の査読） |
| 未着手 | なし |
| 解釈的・メタ主張 | C3.3、C8.1、C10.10（依存関係は点検済み）、§11〜13 |
