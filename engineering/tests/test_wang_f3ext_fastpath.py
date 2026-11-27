"""F₃ 求秩 / 展平秩快路径（Wang 框架 core/rank_f3_fast.h）的等价性回归测试。

背景（2026-11-27）: 框架的通用 DynamicMatrix<3,1>::Rank() 每次调用堆分配 + 全 Gauss–Jordan,
RankLowerBoundFlatten 再做两次循环转置 + 三次堆分配; forced product 每次迭代约 20 µs,
3^18 = 3.87 亿次枚举要 16 分钟。F₃ 扩展给这两处加了快路径（前向消元 + 栈上平铺数组 + 直接按跨度读取）。
本测试编译 engineering/wang_f3ext/standalone/rank_f3_fast_check.cc, 用**独立写的**参考实现做随机对拍。

需要上游副本（WANG_REPO, 缺省 /tmp/wang-tensor-rank）已打补丁; 缺失时跳过（/tmp 易失）。
"""
import hashlib
import os
import platform
import shutil
import subprocess
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
EXT = os.path.join(ROOT, "engineering", "wang_f3ext")
TEST_CC = os.path.join(EXT, "standalone", "rank_f3_fast_check.cc")


def _find_repo():
    repo = os.environ.get("WANG_REPO", "/tmp/wang-tensor-rank")
    if os.path.isdir(os.path.join(repo, "core")) and os.path.exists(os.path.join(repo, "core", "rank_f3_fast.h")):
        return repo
    return None


def _find_cxx():
    for cxx in (os.environ.get("CXX"), "/opt/homebrew/opt/llvm/bin/clang++", shutil.which("clang++"), shutil.which("g++")):
        if cxx and os.path.exists(cxx):
            return cxx
    return None


class WangF3extFastPathTest(unittest.TestCase):
    """F₃ 快路径与独立参考实现在随机输入上逐个相等（求秩 + 展平秩）。"""

    def test_rank_and_flatten_fast_paths_match_reference(self):
        repo = _find_repo()
        if repo is None:
            self.skipTest("上游副本未就绪（WANG_REPO 未打补丁）")
        cxx = _find_cxx()
        if cxx is None:
            self.skipTest("no C++ compiler found")
        with tempfile.TemporaryDirectory() as tmp:
            exe = os.path.join(tmp, "rank_f3_fast_check")
            build = subprocess.run(
                [cxx, "-std=c++23", "-O2", "-DNDEBUG", "-w", "-pthread",
                 "-I" + os.path.join(EXT, "shim"), "-I" + repo, TEST_CC,
                 os.path.join(repo, "core", "dynamic_matrix.cc"), "-o", exe],
                capture_output=True, text=True, timeout=600,
            )
            self.assertEqual(build.returncode, 0, build.stderr[-2000:])
            run = subprocess.run([exe, "4000"], capture_output=True, text=True, timeout=600)
            self.assertEqual(run.returncode, 0, run.stdout[-1500:])
            self.assertIn("mismatches=0", run.stdout)
            self.assertNotIn("MISMATCH", run.stdout)

    def test_get_batch_kernel(self):
        """OrbitMap::Get 的批量探针内核(NEON 16 路 + 标签预筛): 块内核 / 端到端 / 未命中三项对拍 + 微基准(需 ARM64)。"""
        repo = _find_repo()
        if repo is None:
            self.skipTest("上游副本未就绪（WANG_REPO 未打补丁）")
        if platform.machine() not in ("arm64", "aarch64"):
            self.skipTest("批量探针内核的 NEON 版需要 ARM64")
        cxx = _find_cxx()
        if cxx is None:
            self.skipTest("no C++ compiler found")
        src = os.path.join(EXT, "standalone", "get_simd_check.cc")
        with tempfile.TemporaryDirectory() as tmp:
            exe = os.path.join(tmp, "get_simd_check")
            build = subprocess.run(
                [cxx, "-std=c++23", "-O2", "-DNDEBUG", "-w", "-pthread",
                 "-I" + os.path.join(EXT, "shim"), "-I" + repo, src,
                 os.path.join(repo, "core", "dynamic_matrix.cc"), "-o", exe],
                capture_output=True, text=True, timeout=900,
            )
            self.assertEqual(build.returncode, 0, build.stderr[-2000:])
            run = subprocess.run([exe, "60"], capture_output=True, text=True, timeout=900)
            self.assertEqual(run.returncode, 0, run.stdout[-1500:])
            # A 块内核 / B 端到端 / C 未命中 / E 重复行: 四行都必须是 mismatches=0
            self.assertEqual(run.stdout.count("mismatches=0"), 4, run.stdout)
            for section in ("A block kernel", "B orbit map", "C probe-all", "E repeated rows"):
                line = [l for l in run.stdout.splitlines() if l.startswith(section)]
                self.assertEqual(len(line), 1, run.stdout)
                self.assertTrue(line[0].endswith("mismatches=0"), line[0])
            self.assertNotIn("MISMATCH", run.stdout)
            self.assertIn("OK", run.stdout)

    def test_backtracking_dedup_keys_same_as_upstream(self):
        """回溯搜索的「去重键 + 类子集求值」(search/rank_lower_bound_backtracking.h 的 F₃ 分支)与上游行为逐字节相同。

        同一个 lower 二进制跑三种模式: 上游行为(SOVEREIGN_F3_RAWKEYS=1) / 新实现 / 类数阈值调到 3
        (逼出逐 mask 的回退分支)。都从零算 dim 9–6, 证书与 .btp 轨迹档案的 sha256 必须一致。
        需要构建整个 lower(约 1–2 分钟)与库内的 v1 证书; 上游副本缺失时跳过。"""
        repo = _find_repo()
        if repo is None:
            self.skipTest("上游副本未就绪（WANG_REPO 未打补丁）")
        if platform.machine() not in ("arm64", "aarch64"):
            self.skipTest("本测试的参考读数在 ARM64 机器上取得")
        cert_dir = os.path.join(EXT, "certs")
        cert = os.path.join(cert_dir, "matrix_q03_n333_v1.pb.txt")
        btp = os.path.join(cert_dir, "matrix_q03_n333_v1.btp")
        if not (os.path.exists(cert) and os.path.exists(btp)):
            self.skipTest("v1 证书不在库里")
        env = dict(os.environ)
        env.pop("SOVEREIGN_F3_RAWKEYS", None)
        env.pop("SOVEREIGN_F3_MAX_CLASSES", None)
        env["WANG_REPO"] = repo

        def sha(path):
            with open(path, "rb") as f:
                return hashlib.sha256(f.read()).hexdigest()

        with tempfile.TemporaryDirectory() as tmp:
            exe = os.path.join(tmp, "lower_f3")
            build = subprocess.run(["bash", os.path.join(EXT, "build.sh"), "3", "lower", exe],
                                   capture_output=True, text=True, timeout=1800, env=env)
            self.assertEqual(build.returncode, 0, build.stderr[-2000:])
            digests = {}
            for mode, extra in (("raw", {"SOVEREIGN_F3_RAWKEYS": "1"}), ("dedup", {}),
                                ("fallback", {"SOVEREIGN_F3_MAX_CLASSES": "3"})):
                work = os.path.join(tmp, mode)
                os.mkdir(work)
                shutil.copy(cert, os.path.join(work, "c.pb.txt"))
                shutil.copy(btp, os.path.join(work, "c.btp"))
                run_env = dict(env)
                run_env.update(extra)
                run = subprocess.run(
                    [exe, "c.pb.txt", "--ignore_rank_lower_bound", "--dim_min=6",
                     "--backtracking_step_limit=10000000", "--forced_product_max_iterations_log2=28",
                     "--backtracking_max_map_size=2000000"],
                    cwd=work, capture_output=True, text=True, timeout=3600, env=run_env)
                self.assertEqual(run.returncode, 0, run.stderr[-2000:])
                self.assertIn("Processing dim=6", run.stderr)
                digests[mode] = (sha(os.path.join(work, "c.pb.txt")), sha(os.path.join(work, "c.btp")))
            self.assertEqual(digests["dedup"], digests["raw"])
            self.assertEqual(digests["fallback"], digests["raw"])

    def test_group_action_fast_path_matches_naive(self):
        """F₃ 3×3 群作用快路径 vs 独立朴素实现（全量 19683 向量 × 全部群元; 默认抽样步长 17, WANG_SLOW=1 全量）。"""
        repo = _find_repo()
        if repo is None:
            self.skipTest("上游副本未就绪（WANG_REPO 未打补丁）")
        cxx = _find_cxx()
        if cxx is None:
            self.skipTest("no C++ compiler found")
        src = os.path.join(EXT, "standalone", "apply_check.cc")
        with tempfile.TemporaryDirectory() as tmp:
            exe = os.path.join(tmp, "apply_check")
            build = subprocess.run(
                [cxx, "-std=c++23", "-O2", "-DNDEBUG", "-w", "-pthread",
                 "-I" + os.path.join(EXT, "shim"), "-I" + repo, src,
                 os.path.join(repo, "core", "dynamic_matrix.cc"), "-o", exe],
                capture_output=True, text=True, timeout=600,
            )
            self.assertEqual(build.returncode, 0, build.stderr[-2000:])
            stride = "1" if os.environ.get("WANG_SLOW") else "17"
            run = subprocess.run([exe, stride], capture_output=True, text=True, timeout=900)
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr[-800:])
            self.assertIn("mismatches: store=0 query=0 inverse=0 identity=0", run.stdout)


if __name__ == "__main__":
    unittest.main()
