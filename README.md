# FaceSecure (JML)

Projeto de reconhecimento facial utilizando **OpenCV**, refatorado para uma aplicação **Java CLI** (Command Line Interface).

O foco principal desta versão é demonstrar a aplicação de **Verificação Formal** e **Design by Contract** utilizando **OpenJML**.

---

## Pré-requisitos (Linux/Ubuntu)

Para rodar este projeto, você precisa preparar o ambiente.

### 1. Instalar Java 21 (JDK)
```bash
sudo apt update
sudo apt install openjdk-21-jdk
```
### 2 Instalar OpenCV (Nativo)
```bash
sudo apt install libopencv-dev libopencv-java
```

### Preparação do dataset
Antes de compilar, crie a estrutura de pastas para as fotos de treino. O sistema aceita apenas imagens .png
```bash
mkdir -p dataset/1
```
Coloque suas fotos `.png`dentro dessa pasta

## Build:
Na raiz do projeto, execute o comando abaixo para compilar todos os arquivos .java e gerar os .class na pasta target:
```bash
mkdir -p secure/target/classes

javac -cp "/usr/share/java/opencv-460.jar" \
-d secure/target/classes \
secure/src/main/java/com/face/secure/dtos/*.java \
secure/src/main/java/com/face/secure/model/*.java \
secure/src/main/java/com/face/secure/repositories/*.java \
secure/src/main/java/com/face/secure/service/*.java \
secure/src/main/java/com/face/secure/*.java
```

## Treinamento
Antes de detectar rostos, é necessário gerar o arquivo face.yml a partir do dataset. Execute
```bash
java -cp "/usr/share/java/opencv-460.jar:secure/target/classes" \
-Djava.library.path=/usr/lib/jni \
com.face.secure.FaceSecureApplication train
```

## RUn:
Para executar, precisamos dizer ao Java onde estão as classes compiladas E onde está a biblioteca nativa do OpenCV (-Djava.library.path).
```bash
java -cp "/usr/share/java/opencv-460.jar:secure/target/classes" \
-Djava.library.path=/usr/lib/jni \
com.face.secure.FaceSecureApplication detect
```

## Verficação FOrmal (JML)
Certifique-se de ter o OpenJML baixado. Substitua ~/openjml/openjml pelo caminho onde você instalou a ferramenta.
```bash
~/openjml/openjml --esc \
-cp "/usr/share/java/opencv-460.jar" \
-sourcepath secure/src/main/java \
secure/src/main/java/com/face/secure/service/UserService.java > jml_log.txt
```