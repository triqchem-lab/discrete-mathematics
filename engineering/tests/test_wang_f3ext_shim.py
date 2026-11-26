"""Wang 框架手工构建垫片的分块回归测试(tbb::parallel_for / parallel_reduce 的 std::thread 实现)。

背景(2026-11-27): 垫片分块曾有差一错误 —— 只有最后一个线程把区间终点钳到 last, 分块不整除且
末块起点 >= last 时该线程不运行, 于是倒数第二块越过 last(n=13、8 线程时为 [12, 14))。下标越界
读到零向量, 令 F₃ 下界搜索在 dim=6 处 FATAL("Constraints not found in OrbitMap (size=7)")。
F₂ 的各维轨道数(1, 3, 14, 68, 162)恰好都不触发, 所以当时的 F₂ 回归没有暴露。

本测试编译 wang_f3ext/shim_test/parallel_for_test.cc 并对 SHIM_THREADS = 1..8 各跑一遍。
没有 C++ 编译器时跳过。
"""
import os
import shutil
import subprocess
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SHIM_DIR = os.path.join(HERE, "..", "wang_f3ext", "shim")
TEST_CC = os.path.join(HERE, "..", "wang_f3ext", "shim_test", "parallel_for_test.cc")


def _find_cxx():
    for cxx in (os.environ.get("CXX"), "/opt/homebrew/opt/llvm/bin/clang++", shutil.which("clang++"), shutil.which("g++")):
        if cxx and os.path.exists(cxx):
            return cxx
    return None


class WangF3extShimChunkingTest(unittest.TestCase):
    """垫片分块: 每个下标恰好访问一次、块界不越过 [first, last)、归约等于串行结果。"""

    def test_chunking_all_thread_counts(self):
        cxx = _find_cxx()
        if cxx is None:
            self.skipTest("no C++ compiler found")
        if not os.path.exists(TEST_CC):
            self.skipTest("parallel_for_test.cc not found")
        with tempfile.TemporaryDirectory() as tmp:
            exe = os.path.join(tmp, "parallel_for_test")
            build = subprocess.run(
                [cxx, "-std=c++17", "-O2", "-pthread", "-I" + SHIM_DIR, TEST_CC, "-o", exe],
                capture_output=True, text=True, timeout=300,
            )
            self.assertEqual(build.returncode, 0, build.stderr[-2000:])
            for n in range(1, 9):
                env = dict(os.environ, SHIM_THREADS=str(n))
                run = subprocess.run([exe], capture_output=True, text=True, timeout=120, env=env)
                self.assertEqual(run.returncode, 0, f"SHIM_THREADS={n}: {run.stdout}")


if __name__ == "__main__":
    unittest.main()
