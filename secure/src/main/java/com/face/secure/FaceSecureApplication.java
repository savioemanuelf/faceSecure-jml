package com.face.secure;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;

import org.opencv.core.Core;

import com.face.secure.dtos.DetectFacesDTO;
import com.face.secure.repositories.UserRepository;
import com.face.secure.service.ContinuousMonitoringService;
import com.face.secure.service.FaceRecognitionService;
import com.face.secure.service.ModelTrainingService;
import com.face.secure.service.UserService;

public class FaceSecureApplication {

	public static void main(String[] args) {
		System.loadLibrary(Core.NATIVE_LIBRARY_NAME);
		System.out.println("OpenCV loaded successfully - version " + Core.VERSION);

		UserRepository userRepository = new UserRepository();
		UserService userService = new UserService(userRepository);
		FaceRecognitionService faceRecognitionService = new FaceRecognitionService(userService);
		ContinuousMonitoringService monitoringService = new ContinuousMonitoringService(faceRecognitionService);
		ModelTrainingService modelTrainingService = new ModelTrainingService();

		if (args.length == 0) {
			printUsage(args);
			return;
		}

		String command = args[0].toLowerCase();
		switch (command) {
			case "train" -> modelTrainingService.trainFaceRecognizer();
			case "update-model" -> modelTrainingService.addNewDataToModel();
			case "monitor" -> {
				if (args.length < 3) {
					System.err.println("Uso: monitor <intervaloEmMinutos> <tempoLimiteEmMinutos>");
					return;
				}
				int interval = Integer.parseInt(args[1]);
				int limit = Integer.parseInt(args[2]);
				boolean result = monitoringService.startMonitoring(interval, limit);
				System.out.println("Monitoramento finalizado: " + result);
			}
			case "recognize" -> {
				if (args.length < 2) {
					System.err.println("Uso: recognize <caminhoDaImagem>");
					return;
				}
				Path imagePath = Paths.get(args[1]);
				System.out.println(faceRecognitionService.recognize(imagePath));
			}
			case "detect" -> {
				boolean detected = faceRecognitionService.detectFaces();
				System.out.println("Face detectada: " + detected);
			}
			case "detect-info" -> {
				DetectFacesDTO dto = new DetectFacesDTO();
				DetectFacesDTO result = faceRecognitionService.detectFaces(dto);
				if (result != null && result.isFaceDetected()) {
					System.out.println("Resultado: " + result.getName() + " confiança " + result.getConfidence());
				} else {
					System.out.println("Nenhuma face reconhecida.");
				}
			}
			default -> {
				System.err.println("Comando desconhecido: " + command);
				printUsage(args);
			}
		}
	}

	private static void printUsage(String[] args) {
		System.out.println("Comandos disponíveis:");
		System.out.println("  train                 - Treina o modelo com o dataset atual");
		System.out.println("  update-model          - Atualiza o modelo existente com novas imagens");
		System.out.println("  monitor <i> <limit>   - Inicia monitoramento (i=intervalo minutos, limit=tempo máximo minutos)");
		System.out.println("  recognize <imagem>    - Reconhece uma imagem usando o modelo atual");
		System.out.println("  detect                - Detecta faces usando a câmera padrão");
		System.out.println("  detect-info           - Detecta faces e retorna dados detalhados");
		System.out.println("Argumentos recebidos: " + Arrays.toString(args));
	}
}
