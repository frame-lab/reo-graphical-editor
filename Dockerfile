FROM coqorg/coq:8.15.0
RUN sudo apt-get update
RUN sudo apt-get install -y software-properties-common
RUN sudo apt-get update
RUN sudo apt-get install -y python3 pkg-config build-essential libcairo2-dev libpango1.0-dev libjpeg-dev libgif-dev librsvg2-dev nodejs npm
COPY . .
RUN npm i
ARG CACHE=1
RUN sudo make

ENTRYPOINT ["npm", "start"]

