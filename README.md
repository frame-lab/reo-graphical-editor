# ReoXplore
Web-based graphical editor for Reo language integrating [reo2nuXmv](https://github.com/frame-lab/Reo2nuXmv) and [CACoq](https://github.com/frame-lab/CACoq) tools.

## Build in host machine

### Prerequisites
* NodeJS 10.12
* Coq (to generate Haskell code)

Note: The editor is not compatible with Internet Explorer.

### Installing required NodeJS packages
Open a terminal in project's root directory and run command:
```console
$ npm i
```

### Building whit host
In the project's root directory there is a makefile, you can run it with:
```console
$ make
```

## Running
After building the project, run command:
```console
$ npm start
```

## Build with docker

You can also build and run the project using docker.
To build it you can use:
```sh
make docker_build
```

In order to execute it, you can run:
```sh
make docker_run
```

You may also use `make docker_stop` to close the server and `make docker_logs` to watch the logs from the server.

## Help
This sections provides an explanation to the important names in the models.

### nuXmv
- finalAutomata: the MODULE where the final circuit will be represented, so to access the module itself, start from here.
- time: how time is represented in the model, it increments in steps of one.
- ports: the variable that instantiantes the *portsModule*, to access the TDS in a specific time, use finalAutomata.ports.\<port name\>[\<time step\>]
- cs: the varibale that represents the current state of a MODULE, to access a state from the circuit use finalAutomata.cs


## Origin
This repository is a fork of [reo-graphical-editor](https://github.com/ReoLanguage/reo-graphical-editor) project developed by [@AliMirlou](https://github.com/AliMirlou).
