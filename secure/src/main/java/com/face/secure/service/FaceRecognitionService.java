package com.face.secure.service;

import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.Objects;

import org.opencv.core.Core;
import org.opencv.core.Mat;
import org.opencv.core.MatOfRect;
import org.opencv.core.Rect;
import org.opencv.core.Size;
import org.opencv.face.LBPHFaceRecognizer;
import org.opencv.imgcodecs.Imgcodecs;
import org.opencv.imgproc.Imgproc;
import org.opencv.objdetect.CascadeClassifier;
import org.opencv.videoio.VideoCapture;

import com.face.secure.dtos.DetectFacesDTO;

public class FaceRecognitionService {

    private final UserService userService;
    private final CascadeClassifier faceDetector;
    private final Path modelPath;

    public FaceRecognitionService(UserService userService) {
        this(userService, Paths.get("E:/face.yml"));
    }

    public FaceRecognitionService(UserService userService, Path modelPath) {
        this.userService = Objects.requireNonNull(userService, "userService");
        this.modelPath = modelPath;
        this.faceDetector = new CascadeClassifier(resolveCascadePath());
    }

    public String recognize(Path imagePath) {
        LBPHFaceRecognizer faceRecognizer = LBPHFaceRecognizer.create();
        faceRecognizer.read(modelPath.toString());

        Mat testImage = Imgcodecs.imread(imagePath.toString(), Imgcodecs.IMREAD_GRAYSCALE);
        if (!testImage.empty()) {
            int[] label = new int[1];
            double[] confidence = new double[1];

            faceRecognizer.predict(testImage, label, confidence);
            String nome = userService.getNameByLabel(label[0]);
            if(confidence[0] < 30){
                return "predicao" + nome + "confianca" + confidence[0];
            }else{
                return "Face não reconhecida." + confidence[0];
            }
        }
        return "Erro ao carregar a imagem de teste.";
    }

    private void saveFrameForDebugging(Mat frame) {
        
        String timestamp = new SimpleDateFormat("yyyyMMdd_HHmmss").format(new Date());
        String fileName = "E:/frames/debug_frame_" + timestamp + ".png";

        // Salvar o frame como imagem
        Imgcodecs.imwrite(fileName, frame);
        System.out.println("Frame salvo: " + fileName);
    }

    public boolean detectFaces() {
        boolean faceDetected = false;

        VideoCapture capture = new VideoCapture(0);
        if (!capture.isOpened()) {
            System.out.println("Erro ao abrir a câmera.");
            return false;
        }

        LBPHFaceRecognizer faceRecognizer = LBPHFaceRecognizer.create();
        faceRecognizer.read(modelPath.toString());

        Mat frame = new Mat();
        long timelimit = 59000;
        long startTime = System.currentTimeMillis();
        while (true) {

            if (System.currentTimeMillis() - startTime > timelimit) {
                System.out.println("Time limit.");
                break;
            }
            capture.read(frame);
            if (frame.empty()) {
                throw new RuntimeException("Captured frame is empty");
            }
            //saveFrameForDebugging(frame);
            List<Mat> channels = new ArrayList<>();
            Core.split(frame, channels);
            Mat grayFrame = channels.get(0);
            Imgproc.equalizeHist(grayFrame, grayFrame);
            //saveFrameForDebugging(grayFrame);
            MatOfRect faces = new MatOfRect();
            faceDetector.detectMultiScale(grayFrame, faces, 1.1, 3, 0, new Size(30, 30), new Size());
            
            for (Rect face : faces.toArray()) {
                Mat faceROI = new Mat(grayFrame, face);
                int[] label = new int[1];
                double[] confidence = new double[1];
                faceRecognizer.predict(faceROI, label, confidence);
                String nome = userService.getNameByLabel(label[0]);
                System.out.println("Predição: " + nome);
                System.out.println("Confiança: " + confidence[0]);
                if (confidence[0] < 55) {
                    System.out.println("Face detectada: " + nome + " - Confidence " + confidence[0]);
                    faceDetected = true;
                    break;
                } else {
                    System.out.println("Face não reconhecida.");
                }
            }
            if (faceDetected) {
                break;
            }

            try {
                Thread.sleep(1000);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        capture.release();
        return faceDetected;
    }

    public DetectFacesDTO detectFaces(DetectFacesDTO detectFacesDTO) {
        boolean faceDetected = false;

        VideoCapture capture = new VideoCapture(0);
        if (!capture.isOpened()) {
            System.out.println("Erro ao abrir a câmera.");
            return null;
        }

        LBPHFaceRecognizer faceRecognizer = LBPHFaceRecognizer.create();
        faceRecognizer.read(modelPath.toString());

        Mat frame = new Mat();
        long timelimit = 59000;
        long startTime = System.currentTimeMillis();
        while (true) {

            if (System.currentTimeMillis() - startTime > timelimit) {
                System.out.println("Time limit.");
                break;
            }
            capture.read(frame);
            if (frame.empty()) {
                throw new RuntimeException("Captured frame is empty");
            }
            //saveFrameForDebugging(frame);
            List<Mat> channels = new ArrayList<>();
            Core.split(frame, channels);
            Mat grayFrame = channels.get(0);
            Imgproc.equalizeHist(grayFrame, grayFrame);
            //saveFrameForDebugging(grayFrame);
            MatOfRect faces = new MatOfRect();
        faceDetector.detectMultiScale(grayFrame, faces, 1.1, 3, 0, new Size(30, 30), new Size());
            
            for (Rect face : faces.toArray()) {

                Mat faceROI = new Mat(grayFrame, face);
                

                int[] label = new int[1];
                double[] confidence = new double[1];
                faceRecognizer.predict(faceROI, label, confidence);
                String nome = userService.getNameByLabel(label[0]);
                System.out.println("Predição: " + nome);
                System.out.println("Confiança: " + confidence[0]);
                if (confidence[0] < 55) {
                    System.out.println("Face detectada: " + nome + " - Confidence " + confidence[0]);
                    detectFacesDTO.setName(nome);
                    detectFacesDTO.setConfidence(String.valueOf(confidence[0]));
                    detectFacesDTO.setFaceDetected(true);
                    faceDetected = true;
                    break;
                } else {
                    System.out.println("Face não reconhecida.");
                }
            }
            if (faceDetected) {
                break;
            }

            try {
                Thread.sleep(1000);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        capture.release();
        return detectFacesDTO;
    }

    private static String resolveCascadePath() {
        URL resource = FaceRecognitionService.class.getClassLoader().getResource("haarcascade_frontalface_default.xml");
        if (resource == null) {
            throw new IllegalStateException("Não foi possível localizar o arquivo haarcascade_frontalface_default.xml nos recursos.");
        }
        try {
            return Paths.get(resource.toURI()).toFile().getAbsolutePath();
        } catch (URISyntaxException e) {
            throw new IllegalStateException("Falha ao resolver o caminho do classificador Haar.", e);
        }
    }
}
