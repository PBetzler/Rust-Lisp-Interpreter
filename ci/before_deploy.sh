# This script takes care of building your crate and packaging it for release

set -ex

main() {
    local src=$(pwd) \
          stage=

    case $TRAVIS_OS_NAME in
        linux)
            stage=$(mktemp -d)
            ;;
        osx)
            stage=$(mktemp -d -t tmp)
            ;;
    esac

    test -f Cargo.lock || cargo generate-lockfile

    # TODO Update this to build the artifacts that matter to you
    cross build --target $TARGET --release

	case $TRAVIS_OS_NAME in
        linux)
			cp target/$TARGET/release/lisp_interpreter $stage/

			cd $stage
			tar czf $src/$CRATE_NAME-$TRAVIS_TAG-$TARGET.tar.gz *
            ;;
		osx)
            cp target/$TARGET/release/lisp_interpreter $stage/

			cd $stage
			tar czf $src/$CRATE_NAME-$TRAVIS_TAG-$TARGET.tar.gz *
            ;;
		windows)
			cp target/$TARGET/release/lisp_interpreter.exe $src/$CRATE_NAME-$TRAVIS_TAG-$TARGET.exe
			cd $stage
			;;
    esac
    
    cd $src

    rm -rf $stage
}

main
