AGDA = agda +RTS -M8G -H6G -A128M -RTS
BUILD ?= _build

# 仓库里有同名目录 `test/` ⇒ 不声明 .PHONY 时 make 会判定目标"已是最新"而空跑
.PHONY: test recheck-chain

# 2026-10-26 修：原清单有 28 条指向重组前的旧布局（Sovereign/<Area> →
# Sovereign/{Algebra,Synthesis,Application}/<Area>），已按 basename 逐一重映射
# （46 条全部存在且唯一）。
MODULES = \
	src/Sovereign/Algebra/FieldTower/TriCycGraph.agda \
	src/Sovereign/Synthesis/Combinatorics/ArthurMagicSquare.agda \
	src/Sovereign/Synthesis/Physics/MotorStableStates.agda \
	src/Sovereign/Application/Physics/QuantumMotor.agda \
	src/Sovereign/Algebra/FieldTower/TriadicHarmonic.agda \
	src/Sovereign/Algebra/NumberTheory/DigitalRootCycle.agda \
	src/Sovereign/Algebra/GroupTheory/C3Orbit.agda \
	src/Sovereign/Application/Geometry/ProjectiveCore.agda \
	src/Sovereign/Application/Geometry/ProjectiveOrbit.agda \
	src/Sovereign/Application/Geometry/ProjectiveInvariants.agda \
	src/Sovereign/Application/Geometry/ProjectiveTransform.agda \
	src/Sovereign/Application/Geometry/ConformalCore.agda \
	src/Sovereign/Application/Geometry/ConformalInvariants.agda \
	src/Sovereign/Application/Geometry/TorusGeometry.agda \
	src/Sovereign/Application/Geometry/TorusGeodesic.agda \
	src/Sovereign/Application/Geometry/TorusAlgebra.agda \
	src/Sovereign/Application/Geometry/TorusFourier.agda \
	src/Sovereign/Synthesis/Combinatorics/GF4AffineMagicSquare.agda \
	src/Sovereign/Synthesis/Combinatorics/GF9AffineMagicSquare.agda \
	src/Sovereign/Synthesis/Combinatorics/DynamicMagicSquare.agda \
	src/Sovereign/Synthesis/Representation/SL23Cayley.agda \
	src/Sovereign/Synthesis/A4/BinaryTetrahedralIrreducibility.agda \
	src/Sovereign/Application/Physics/DiscreteStatMech.agda \
	src/Sovereign/Synthesis/Format/Positional.agda \
	src/Sovereign/Synthesis/Format/Doz.agda \
	src/Sovereign/Synthesis/NumberTheory/DigitField.agda \
	src/Sovereign/Synthesis/NumberTheory/DigitRealization.agda \
	src/Sovereign/Application/Problems/ABC/ABCL1.agda \
	src/Sovereign/Algebra/GF9FrobeniusC4.agda \
	src/Sovereign/Algebra/GroupTheory/BraidGroup.agda \
	src/Sovereign/Algebra/GroupTheory/Word.agda \
	src/Sovereign/Algebra/GroupTheory/BraidCongruence.agda \
	src/Sovereign/Algebra/GroupTheory/BraidToSL23.agda \
	src/Sovereign/Algebra/GroupTheory/BraidQuotient.agda \
	src/Sovereign/Algebra/LinearAlgebra/Matrix2Laws.agda \
	src/Sovereign/Synthesis/Representation/Fin3Semiring.agda \
	src/Sovereign/Synthesis/Representation/Matrix2Inverse.agda \
	src/Sovereign/Synthesis/Representation/Matrix2DetMul.agda \
	src/Sovereign/Synthesis/Representation/SL2SetoidGroup.agda \
	src/Sovereign/Synthesis/Representation/SetoidFreeGroupUniversal.agda \
	src/Sovereign/Synthesis/Representation/SL2Bridge.agda \
	src/Sovereign/Synthesis/Representation/BraidGroupSetoid.agda \
	src/Sovereign/Synthesis/Representation/BraidQuotientRec.agda \
	src/Sovereign/Synthesis/Representation/BraidQuotientCubical.agda \
	src/Sovereign/Synthesis/Representation/BraidQuotientCubicalEval.agda \
	src/Sovereign/Synthesis/Representation/BraidQuotientCubicalGroup.agda \
	src/Sovereign/Synthesis/A4/CoverA4.agda \
	src/Sovereign/Synthesis/A4/BilinearSchur2A4.agda \
	src/Sovereign/Synthesis/A4/CharTable2A4.agda \
	src/Sovereign/Synthesis/A4/ToA4Hom.agda \
	src/Sovereign/Synthesis/A4/CharProvenance.agda \
	src/Sovereign/Synthesis/A4/SL23Inverse.agda \
	src/Sovereign/Synthesis/A4/SL23Group.agda

# 快速门：吃缓存。Agda 2.9 对 up-to-date 模块静默跳过（不打印 Skipping），
# 故本目标成功的含义是「路径可解析 + 接口与源码一致」，不等于「现在能过」。
test:
	@set -e; for m in $(MODULES); do $(AGDA) $$m; done
	@echo "ALL_PASS"

# 强证据门：逐个删掉**本模块自己**的接口再常规编译，依赖仍走缓存。
# 不用 --ignore-interfaces：该 flag 的语义是 "re-type check everything"，
# 会把 946 个项目模块 + 1188 个 stdlib 模块全重编。
# 接口路径形如 $(BUILD)/<agda-version>/agda/src/Sovereign/...\.agdai，
# 故用 $(BUILD)/*/agda/ 匹配版本目录，避免把 Agda 版本号写死在这里。
recheck-chain:
	@set -e; for m in $(MODULES); do \
	  rm -f $(BUILD)/*/agda/$${m%.agda}.agdai; \
	  $(AGDA) $$m; \
	done
	@echo "ALL_PASS (recheck-chain)"
