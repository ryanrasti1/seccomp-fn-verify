{
  description = "seccomp-fn-verify: the proof that a seccomp filter's program is its policy (run_bpf, policy!), and kaniCheck, its proofs as a derivation";

  # The revision is flake.lock's.
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      # Kani's release bundle is x86_64 Linux's.
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};

      # Kani, the Rust model checker (github.com/model-checking/kani): not in nixpkgs. Its
      # prebuilt release bundle (kani-compiler, kani-driver, CBMC, kissat, Kani's std) plus the
      # nightly toolchain it was built against, which `cargo kani setup` would fetch with rustup:
      # here the same components from static.rust-lang.org, pinned by hash, laid out where
      # kani-compiler's RUNPATH looks ($ORIGIN/../toolchain). autoPatchelfHook fixes the
      # interpreters and library paths for Nix.
      kani =
        let
          version = "0.68.0";
          # The bundle's rust-toolchain-version: nightly-2026-08-21.
          date = "2026-08-21";
          component = name: sha256: pkgs.fetchurl {
            url = "https://static.rust-lang.org/dist/${date}/${name}-nightly${if name == "rust-src" then "" else "-x86_64-unknown-linux-gnu"}.tar.xz";
            inherit sha256;
          };
          components = [
            (component "rustc" "1d4lap2393wyzswc0ncksh956mcndimjh3ay91d2ndjilmgq2cg5")
            (component "cargo" "0mwwadyajyfv31n0n8xd6ill1inbl2v17cvzf83shzmdf36nsc2i")
            (component "rust-std" "18x35ssy6z2gw3w3vx8kjsml9kdiv8ghcghp0hypr5kg1ibi5kaj")
            (component "rustc-dev" "1nqvyxka8r1qm43fxr72r0b57qfbnpp6i9bfgm0c9hvx8jviynhp")
            (component "rust-src" "1kgq89wzd4mdi9wfd32bhxz58l8hjibvzp50kbphdgsh7ib4jbdp")
          ];
        in
        pkgs.stdenv.mkDerivation {
          pname = "kani";
          inherit version;
          src = pkgs.fetchurl {
            url = "https://github.com/model-checking/kani/releases/download/kani-${version}/kani-${version}-x86_64-unknown-linux-gnu.tar.gz";
            sha256 = "1ls3g2pfk3a4gpk4xv4agm4j5515qiwhikx2cjzhppiysy2b9qij";
          };
          nativeBuildInputs = [ pkgs.autoPatchelfHook pkgs.makeWrapper ];
          buildInputs = [ pkgs.stdenv.cc.cc.lib pkgs.zlib ];
          dontConfigure = true;
          dontBuild = true;
          dontStrip = true;
          installPhase = ''
            runHook preInstall
            mkdir -p $out
            cp -r . $out/
            # Each dist tarball holds component directories (its `components` file) whose trees
            # merge into one toolchain, as rustup's install.sh would lay them out.
            mkdir -p $out/toolchain
            for t in ${toString components}; do
              d=$(mktemp -d)
              tar xJf $t -C $d
              top=$(echo $d/*)
              for c in $(cat $top/components); do cp -r $top/$c/. $out/toolchain/; done
              rm -rf $d
            done
            rm -f $out/toolchain/manifest-*
            # kani-driver is cargo-kani or kani by its name; the toolchain's cargo and rustc come
            # first, and gcc (goto-cc preprocesses Kani's C stubs with it).
            for n in cargo-kani kani; do
              makeWrapper $out/bin/kani-driver $out/bin/$n --argv0 $n \
                --prefix PATH : $out/toolchain/bin:$out/bin:${pkgs.gcc}/bin
            done
            runHook postInstall
          '';
          meta.description = "Kani ${version}, its bundle and toolchain";
        };

      # A derivation that runs `cargo kani` on a crate's `policy!` harnesses (each policy function
      # equal to its program, for every input and every param) and fails if any proof fails.
      # `src` is a Cargo workspace, `cargoLock` its lock file (its dependencies are vendored from
      # it: no network); each of `runs` is one `cargo kani` invocation's arguments, from `src`'s
      # root. `expectHarnesses`: every harness that must have been checked, by its full name
      # (`policies::abi::policy_proof::policy_is_filter`); the build fails if one wasn't, and a
      # run that checked any harness failing fails it (cargo kani's status), so each listed one
      # passed. (Without it a run that found no harness, a filter's `--harness` or a missing
      # `cfg`, passed.) An argument `--no-unwinding-assertions` is refused: with it a bound shorter
      # than the program passes. Its output holds each run's log and a summary of the harnesses.
      kaniCheck = { name, src, cargoLock, runs, expectHarnesses }:
        let
          lib = pkgs.lib;
          unsound = lib.filter (a: lib.hasPrefix "--no-unwinding-assertions" a) (lib.concatLists runs);
        in
        assert lib.assertMsg (unsound == [ ]) "kaniCheck ${name}: --no-unwinding-assertions would pass a bound shorter than a program";
        assert lib.assertMsg (expectHarnesses != [ ]) "kaniCheck ${name}: expectHarnesses is empty: a run that proves nothing would pass";
        pkgs.stdenv.mkDerivation {
          inherit name src;
          # git dependencies (seccomp-fn-verify's own, by rev) fetched at evaluation with the
          # evaluator's credentials: the repositories are private.
          cargoDeps = pkgs.rustPlatform.importCargoLock { lockFile = cargoLock; allowBuiltinFetchGit = true; };
          nativeBuildInputs = [ pkgs.rustPlatform.cargoSetupHook kani ];
          dontConfigure = true;
          # Kani's driver and its cargo want a writable HOME.
          buildPhase = ''
            runHook preBuild
            export HOME=$TMPDIR
            set -o pipefail
            i=0
            ${lib.concatMapStrings (args: ''
              i=$((i + 1))
              echo "cargo kani ${lib.escapeShellArgs args}" | tee kani-$i.log
              # cargo-kani itself: the build has no cargo of its own on PATH for `cargo kani`
              cargo-kani ${lib.escapeShellArgs args} 2>&1 | tee -a kani-$i.log
            '') runs}
            # each expected harness checked (`-j` prefixes its lines with `Thread N: `)
            sed -n 's/^\(Thread [0-9]*: \)\?Checking harness \(.*\)\.\.\.$/\2/p' kani-*.log | sort > checked
            for h in ${lib.escapeShellArgs expectHarnesses}; do
              grep -qxF "$h" checked || { echo "kaniCheck: harness $h wasn't checked"; exit 1; }
            done
            runHook postBuild
          '';
          installPhase = ''
            mkdir -p $out
            cp kani-*.log checked $out/
            grep -h -e '^cargo kani' -e 'Checking harness' -e 'VERIFICATION:' -e 'Verification Time' \
              -e '^Complete' -e 'harnesses' kani-*.log > $out/summary
          '';
        };

      src = pkgs.lib.fileset.toSource {
        root = ./.;
        # not target/ (a build outside a git tree sees it)
        fileset = pkgs.lib.fileset.unions [ ./Cargo.toml ./Cargo.lock ./src ./tests ];
      };
    in
    {
      # `kaniCheck { name, src, cargoLock, runs, expectHarnesses }`: a consumer's proofs as a
      # derivation (seccomp-fn's examples', unsharek-tcb's policy); `kani`.
      lib = { inherit kaniCheck kani; };

      packages.${system} = {
        inherit kani;
        default = kani;
      };

      checks.${system} = {
        # The tests: run_bpf sampled, and against the build machine's kernel.
        tests = pkgs.rustPlatform.buildRustPackage {
          pname = "seccomp-fn-verify-tests";
          version = "0.0.0";
          inherit src;
          cargoLock = { lockFile = ./Cargo.lock; allowBuiltinFetchGit = true; };
          installPhase = "touch $out";
        };
      };

      devShells.${system}.default = pkgs.mkShell {
        packages = [ pkgs.cargo pkgs.rustc pkgs.clippy pkgs.rustfmt kani ];
      };
    };
}
