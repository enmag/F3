FROM ubuntu:20.04
ARG DEBIAN_FRONTEND=noninteractive

# Prepare directory and copy F3 code and resources in it.
RUN mkdir /home/F3
COPY . /home/F3

# Install required packages.
RUN apt-get -y update; apt-get -y upgrade; apt-get -y dist-upgrade; apt-get -y install python3 python3-pip git libgmp-dev swig; apt-get -y autoremove; apt-get -y autoclean
# python is python3
RUN update-alternatives --install /usr/bin/python python /usr/bin/python3 10

# download Pysmt source code
RUN git clone https://github.com/EnricoMagnago/pysmt.git /home/pysmt
# Use nonlinear branch for pysmt, install solvers and accept their licenses.
RUN cd /home/pysmt; git checkout nonlinear; python ./setup.py install; pysmt-install --z3 --msat --confirm-agreement

# install mathsat header and library.
RUN cp /root/.smt_solvers/msat/mathsat-5.6.6-linux-x86_64/include/mathsat.h /usr/include/mathsat.h
RUN cp /root/.smt_solvers/msat/mathsat-5.6.6-linux-x86_64/lib/libmathsat.a /usr/lib/libmathsat.a
# set the correct path to mathsat.h in ltl.i
RUN patch /home/F3/src/ltl/ltl.i /home/F3/ltl_i.patch

# Build swig module for LTL tableau construction.
RUN cd /home/F3/src/ltl; ./swig_release_build.sh

ENTRYPOINT ["/usr/bin/python", "-O", "/home/F3/src/run_f3.py"]
