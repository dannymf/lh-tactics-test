FROM --platform=linux/amd64 ubuntu:20.04

## BEGIN: RUNS AS ROOT

# Create a user

ARG USERNAME=dannymf
ARG USER_UID=1000
ARG USER_GID=$USER_UID

RUN groupadd --gid $USER_GID $USERNAME \
    && useradd --uid $USER_UID --gid $USER_GID -m $USERNAME --shell /bin/zsh \
    #
    # [Optional] Add sudo support. Omit if you don't need to install software after connecting.
    && apt-get update -y \
    && apt-get install -y sudo \
    && echo $USERNAME ALL=\(root\) NOPASSWD:ALL > /etc/sudoers.d/$USERNAME \
    && chmod 0440 /etc/sudoers.d/$USERNAME

## Hack needs root permissions

# See hack.sh
COPY hack.sh /tmp/hack.sh
RUN chmod +x /tmp/hack.sh
RUN /tmp/hack.sh

RUN apt-get install -y build-essential
RUN apt-get install -y m4
RUN apt-get install -y git
RUN apt-get install -y clang
RUN apt-get install -y time
RUN apt-get install -y zip
RUN apt-get install -y zsh
RUN apt-get install -y curl
RUN apt-get install -y python
RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
RUN curl -sSL https://get.haskellstack.org/ | sh
# RUN ghcup install hls

## Set up user environmnent
COPY .zshrc /home/root/
COPY .zshrc /home/$USERNAME/

WORKDIR /workspaces
RUN git clone https://github.com/Z3Prover/z3/
WORKDIR z3
RUN git checkout 517d907567f4283ad8b48ff9c2a3f6dce838569e
RUN python scripts/mk_make.py
WORKDIR build
RUN make
RUN sudo make install
ENV PATH="${PATH}:/workspaces"
ENV PATH="${PATH}:/root/.local/bin/"
ENV PATH="${PATH}:/root/.ghcup/bin"

COPY lh-tactics.cabal-correct /workspaces/lh-tactics-test/lh-tactics/lh-tactics.cabal
WORKDIR /workspaces/lh-tactics-test/lh-tactics
CMD ["sh", "-c", "stack build; stack install"]
# RUN stack install haskell-language-server