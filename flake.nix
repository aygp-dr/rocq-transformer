{
  description = "Rocq Annotated Transformer - Formally verified transformer architecture";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        coq = pkgs.coq_8_18;

        coqPackages = pkgs.coqPackages_8_18;

      in {
        packages = {
          default = pkgs.stdenv.mkDerivation {
            pname = "rocq-transformer";
            version = "0.1.0";

            src = ./.;

            nativeBuildInputs = [ coq ];

            buildPhase = ''
              make all
            '';

            installPhase = ''
              mkdir -p $out/lib/coq/${coq.coq-version}/user-contrib/RocqTransformer
              cp -r RocqTransformer/*.vo $out/lib/coq/${coq.coq-version}/user-contrib/RocqTransformer/
              cp -r RocqTransformer/*.glob $out/lib/coq/${coq.coq-version}/user-contrib/RocqTransformer/
            '';

            meta = with pkgs.lib; {
              description = "Formally verified Transformer architecture in Rocq/Coq";
              license = licenses.mit;
              maintainers = [ ];
            };
          };
        };

        devShells.default = pkgs.mkShell {
          name = "rocq-transformer-dev";

          buildInputs = [
            coq
            coqPackages.coqide  # Optional: CoqIDE for interactive development
          ];

          shellHook = ''
            echo "Rocq Transformer Development Environment"
            echo ""
            echo "Coq version: $(coqc --version | head -1)"
            echo ""
            echo "Available commands:"
            echo "  make          - Build all modules"
            echo "  make clean    - Clean build artifacts"
            echo "  coqide        - Launch CoqIDE"
            echo ""
          '';
        };

        # For `nix check`
        checks.default = self.packages.${system}.default;
      });
}
