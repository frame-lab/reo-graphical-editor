TAG=latest
project=reoxplore
IMAGE=$(project):$(TAG)
cache=4

all:
	make -C Reo2nuXmv
	make -C CACoq
	npm run build:dev

docker_build:
	docker build --build-arg CACHE=$(cache) -t $(IMAGE) .

docker_run: docker_stop docker_build
	docker run --rm -d --name $(project) --env-file docker.env -p 8081:8081 $(IMAGE)

docker_stop:
	docker stop $(project) || true

docker_logs:
	docker logs --tail 100 -f $(project) 

