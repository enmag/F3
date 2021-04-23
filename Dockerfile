FROM ubuntu:20.04
ARG DEBIAN_FRONTEND=noninteractive
# Prepare directory and copy F3 code and resources in it.
RUN mkdir /home/F3
COPY . /home/F3
# Install required packages.
RUN apt-get -y update; apt-get -y upgrade; apt-get -y dist-upgrade
RUN apt-get -y install python3 python3-pip git autoconf flex bison libpcre3 libpcre3-dev libgmp-dev swig
RUN apt-get -y autoremove; apt-get -y autoclean
# python is python3
RUN update-alternatives --install /usr/bin/python python /usr/bin/python3 10
RUN update-alternatives --install /usr/bin/pip pip /usr/bin/pip3 10
# download Pysmt source code
RUN git clone https://github.com/EnricoMagnago/pysmt.git /home/pysmt
# apply patch to use more recent version of z3 and msat. Install solvers and accept their licenses.
RUN cd /home/pysmt; git checkout nonlinear; git apply /home/F3/pysmt.patch; python3 ./setup.py install; pysmt-install --z3 --msat --confirm-agreement
# install mathsat header and library.
RUN cp /root/.smt_solvers/msat/mathsat-5.6.6-linux-x86_64/include/mathsat.h /usr/include/mathsat.h
RUN cp /root/.smt_solvers/msat/mathsat-5.6.6-linux-x86_64/lib/libmathsat.a /usr/lib/libmathsat.a
# install python dependency.
RUN pip3 install timeout-decorator
# set the correct path to mathsat.h in ltl.i
RUN patch /home/F3/src/ltl/ltl.i /home/F3/f3_ltl_i.patch
# Build swig module for LTL tableau construction.
RUN cd /home/F3/src/ltl; ./swig_release_build.sh

ENTRYPOINT ["/usr/bin/python", "-O", "/home/F3/src/run_benchmarks.py"]
