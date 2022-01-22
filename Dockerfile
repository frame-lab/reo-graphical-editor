FROM node:10.12-slim
RUN apt update
RUN apt install -y software-properties-common
#RUN add-apt-repository ppa:deadsnakes/ppa
RUN apt update
RUN apt install -y python3 pkg-config build-essential libcairo2-dev libpango1.0-dev libjpeg-dev libgif-dev librsvg2-dev 
COPY . .
RUN npm i
ARG CACHE=1
RUN make

#EXPOSE 8081

ENTRYPOINT ["npm", "start"]

