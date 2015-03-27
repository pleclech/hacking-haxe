package io;

import sys.io.Process;

class TestProcess extends haxe.unit.TestCase {
	#if !php
	function testArguments() {
		var bin = sys.FileSystem.absolutePath(TestArguments.bin);
		var args = TestArguments.expectedArgs;

		var process = new Process("haxe", ["compile-each.hxml", "--run", "TestArguments"].concat(args));
		var exitCode = process.exitCode();
		if (exitCode != 0)
			trace(sys.io.File.getContent(TestArguments.log));
		assertEquals(0, exitCode);

		var process =
			#if (macro || interp)
				new Process("haxe", ["compile-each.hxml", "--run", "TestArguments"].concat(args));
			#elseif cpp
				new Process(bin, args);
			#elseif cs
				switch (Sys.systemName()) {
					case "Windows":
						new Process(bin, args);
					case _:
						new Process("mono", [bin].concat(args));
				}
			#elseif java
				new Process("java", ["-jar", bin].concat(args));
			#elseif python
				new Process("python3", [bin].concat(args));
			#elseif neko
				new Process("neko", [bin].concat(args));
			#elseif php
				new Process("php", [bin].concat(args));
			#else
				null;
			#end
		var exitCode = process.exitCode();
		if (exitCode != 0)
			trace(sys.io.File.getContent(TestArguments.log));
		assertEquals(0, exitCode);
	}
	#end

	function testExitCode() {
		var bin = sys.FileSystem.absolutePath(ExitCode.bin);

		// Just test only a few to save time.
		// They have special meanings: http://tldp.org/LDP/abs/html/exitcodes.html
		var codes = [0, 1, 2, 126, 127, 128, 130, 255];

		for (code in codes) {
			var args = [Std.string(code)];
			var process = new Process("haxe", ["compile-each.hxml", "--run", "ExitCode"].concat(args));
			assertEquals(code, process.exitCode());
		}

		for (code in codes) {
			var args = [Std.string(code)];
			var process =
				#if (macro || interp)
					new Process("haxe", ["compile-each.hxml", "--run", "ExitCode"].concat(args));
				#elseif cpp
					new Process(bin, args);
				#elseif cs
					switch (Sys.systemName()) {
						case "Windows":
							new Process(bin, args);
						case _:
							new Process("mono", [bin].concat(args));
					}
				#elseif java
					new Process("java", ["-jar", bin].concat(args));
				#elseif python
					new Process("python3", [bin].concat(args));
				#elseif neko
					new Process("neko", [bin].concat(args));
				#elseif php
					new Process("php", [bin].concat(args));
				#else
					null;
				#end
			assertEquals(code, process.exitCode());
		}
	}
}