# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.145.1/containers/ubuntu/.devcontainer/base.Dockerfile

# [Choice] Ubuntu version: bionic, focal
ARG VARIANT="focal"
FROM mcr.microsoft.com/vscode/devcontainers/base:0-${VARIANT}
ENV DEBIAN_FRONTEND=noninteractive

ENV LANG     C.UTF-8
ENV LC_ALL   C.UTF-8
ENV LANGUAGE C.UTF-8

# [Optional] Uncomment this section to install additional OS packages.
# RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
#     && apt-get -y install --no-install-recommends <your-package-list-here>

# Configure apt and install packages
RUN apt-get update && apt-get upgrade -y
RUN apt-get -y install --no-install-recommends apt-utils 2>&1 \
    #
    # Verify git, process tools, lsb-release (common in install instructions for CLIs) installed
    && apt-get -y install git procps lsb-release \
    && apt-get -y install curl wget screen build-essential \
    && apt-get -y install python make \
    && apt-get install -y gnupg gpgv


# Install z3 Prover
RUN git clone --branch z3-4.7.1 https://github.com/Z3Prover/z3.git \
    && cd z3 \
    && python scripts/mk_make.py \
    && cd build \
    && make \
    && make install

# Set up LSP for Haskell
RUN mkdir -p $HOME/.local/bin
RUN apt-get -y install --no-install-recommends apt-utils 2>&1 \
    && apt-get -y install libicu-dev libtinfo-dev libgmp-dev libncurses-dev zlib1g-dev

RUN apt-get -y install libtinfo5 \
    # mentioned on the GHC wiki
    autoconf automake libtool make libgmp-dev ncurses-dev g++ python bzip2 ca-certificates \
    xz-utils \
    ## install minimal set of haskell packages
    # from darinmorrison/haskell
    xutils-dev python3 time

RUN curl -sSL https://get.haskellstack.org/ | sh

RUN cd /usr/local/bin \
    && curl -O https://downloads.haskell.org/~ghcup/0.1.11/x86_64-linux-ghcup-0.1.11 \
    && mv x86_64-linux-ghcup-0.1.11 ghcup \
    && chmod +x ghcup

RUN ghcup upgrade \
    && ghcup install ghc 8.8.4 \
    && ghcup set ghc 8.8.4 \
    && ghcup install cabal

ENV PATH /root/.local/bin/:$PATH
ENV PATH /root/.ghcup/bin/:$PATH
ENV PATH /root/.cabal/bin/:$PATH







