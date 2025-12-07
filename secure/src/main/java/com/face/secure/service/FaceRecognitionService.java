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

    //@ public invariant userService != null;
    //@ public invariant faceDetector != null;
    //@ public invariant modelPath != null;

    /*@ spec_public non_null @*/
    private final UserService userService; 
    /*@ spec_public non_null @*/
    private final CascadeClassifier faceDetector; 
    /*@ spec_public non_null @*/
    private final Path modelPath; 

    //@ public ghost int attemptCount;

    /*@
      @ public behavior
      @ requires userService != null;
      @ ensures this.userService == userService;
      @ ensures this.modelPath != null;
      @ ensures this.attemptCount == 0;
      @ signals (Exception e) true;
      @*/
    public FaceRecognitionService(UserService userService) {
        this(userService, Paths.get("face.yml"));
	//@ set attemptCount = 0;
    }

    /*@
      @ public behavior
      @ requires userService != null;
      @ requires modelPath != null;
      @ ensures this.userService == userService;
      @ ensures this.modelPath == modelPath;
      @ ensures this.faceDetector != null;
      @ ensures this.attemptCount == 0;
      @ signals (Exception e) true;
      @ skipesc
      @*/
    public FaceRecognitionService(UserService userService, Path modelPath) {
        this.userService = Objects.requireNonNull(userService, "userService");
        this.modelPath = modelPath;
        this.faceDetector = new CascadeClassifier(resolveCascadePath());
        //@ set attemptCount = 0;
    }

    /*@
      @ public normal_behavior
      @ requires imagePath != null;
      @ ensures \result != null;
      @ skipesc
      @*/
    public String recognize(Path imagePath) {
        LBPHFaceRecognizer faceRecognizer = LBPHFaceRecognizer.create();
        faceRecognizer.read(modelPath.toString());

        Mat testImage = Imgcodecs.imread(imagePath.toString(), Imgcodecs.IMREAD_GRAYSCALE);
        if (!testImage.empty()) {
            int[] label = new int[1];
            double[] confidence = new double[1];

            faceRecognizer.predict(testImage, label, confidence);
            String nome = userService.getNameByLabel(label[0]);
            if (confidence[0] < 30) {
                return "predicao" + nome + " confianca " + confidence[0];
            } else {
                return "Face não reconhecida." + confidence[0];
            }
        }
        return "Erro ao carregar a imagem de teste.";
    }

    /*@
      @ private behavior
      @ requires frame != null;
      @ skipesc
      @*/
    private void saveFrameForDebugging(Mat frame) {
        String timestamp = new SimpleDateFormat("yyyyMMdd_HHmmss").format(new Date());
        String fileName = "E:/frames/debug_frame_" + timestamp + ".png";

        Imgcodecs.imwrite(fileName, frame);
        System.out.println("Frame salvo: " + fileName);
    }

    /*@
      @ public behavior
      @ assignable \nothing;
      @ ensures \result == true || \result == false;
      @ signals (Exception e) true;
      @*/
    public /*@ skipesc @*/ boolean detectFaces() {

        VideoCapture capture = new VideoCapture(0);
        if (!capture.isOpened()) {
            System.out.println("Erro ao abrir a câmera.");
            return false;
        }
	Mat frame = new Mat();
    	capture.read(frame); // Lê apenas UM frame
    
    	boolean faceDetected = false;

    	if (!frame.empty()) {
        	List<Mat> channels = new ArrayList<>();
        	Core.split(frame, channels);
        	Mat grayFrame = channels.get(0);
       		Imgproc.equalizeHist(grayFrame, grayFrame);
        	MatOfRect faces = new MatOfRect();
        
        
        	faceDetector.detectMultiScale(grayFrame, faces, 1.1, 3, 0, new Size(30, 30), new Size());
        
        	if (faces.toArray().length > 0) {
		faceDetected = true; 
        	}
    	}
    
    	capture.release(); 
    	return faceDetected;

    }

    /*@
      @ public behavior
      @ requires detectFacesDTO != null;
      @ ensures \result == detectFacesDTO;
      @ signals_only java.lang.RuntimeException;
      @ skipesc
      @*/
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

	/*@ 
          @ loop_invariant System.currentTimeMillis() >= startTime;
          @ loop_invariant detectFacesDTO != null;
          @ loop_modifies detectFacesDTO.name, detectFacesDTO.confidence, detectFacesDTO.faceDetected, attemptCount;
          @*/
        while (true) {
		//@ set attemptCount = attemptCount + 1;

            if (System.currentTimeMillis() - startTime > timelimit) {
                System.out.println("Time limit.");
                break;
            }
            capture.read(frame);
            if (frame.empty()) {
                break;
            }

            List<Mat> channels = new ArrayList<>();
            Core.split(frame, channels);

            if (channels.isEmpty())
                break;

            Mat grayFrame = channels.get(0);
            Imgproc.equalizeHist(grayFrame, grayFrame);
            MatOfRect faces = new MatOfRect();
            faceDetector.detectMultiScale(grayFrame, faces, 1.1, 3, 0, new Size(30, 30), new Size());

	    Rect[] facesArray = faces.toArray();

            /*@
              @ loop_invariant k >= 0 && k <= facesArray.length;
              @ loop_invariant faceDetected ==> detectFacesDTO.faceDetected;
              @*/
            for (int k = 0; k < facesArray.length; k++) {
                Rect face = facesArray[k];
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

    /*@
      @ private normal_behavior
      @ ensures \result != null;
      @ also
      @ private exceptional_behavior
      @ signals (IllegalStateException) true;
      @ skipesc
      @*/
    private static String resolveCascadePath() {
        URL resource = FaceRecognitionService.class.getClassLoader().getResource("haarcascade_frontalface_default.xml");
        if (resource == null) {
            throw new IllegalStateException(
                "Não foi possível localizar o arquivo haarcascade_frontalface_default.xml nos recursos.");
        }
        try {
            return Paths.get(resource.toURI()).toFile().getAbsolutePath();
        } catch (URISyntaxException e) {
            throw new IllegalStateException("Falha ao resolver o caminho do classificador Haar.", e);
        }
    }
}
