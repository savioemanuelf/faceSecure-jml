package com.face.secure.service;

import java.io.File;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.opencv.core.CvType;
import org.opencv.core.Mat;
import org.opencv.core.MatOfRect;
import org.opencv.core.Rect;
import org.opencv.core.Size;
import org.opencv.face.LBPHFaceRecognizer;
import org.opencv.imgcodecs.Imgcodecs;
import org.opencv.imgproc.Imgproc;
import org.opencv.objdetect.CascadeClassifier;

public class ModelTrainingService {
    
    private /*@ spec_public non_null @*/ final CascadeClassifier faceDetector;
    private /*@ spec_public non_null @*/ final File datasetDirectory;
    private /*@ spec_public non_null @*/ final Path modelPath;
    
    //@ public invariant faceDetector != null;
    //@ public invariant datasetDirectory != null;
    //@ public invariant modelPath != null;

    /*@ public behavior
      @   ensures this.datasetDirectory != null;
      @   ensures this.modelPath != null;
      @   signals (Exception e) true;
      @*/
    public ModelTrainingService() {
        this(new File("dataset"), Paths.get("face.yml"));
    }

    /*@ public behavior
      @   requires datasetDirectory != null;
      @   requires modelPath != null;
      @   ensures this.datasetDirectory == datasetDirectory;
      @   ensures this.modelPath == modelPath;
      @   signals (Exception e) true; 
      @*/
    public ModelTrainingService(File datasetDirectory, Path modelPath) {
        this.datasetDirectory = datasetDirectory;
        this.modelPath = modelPath;
        
        String path = resolveCascadePath();
        this.faceDetector = new CascadeClassifier(path);
    }

    /*@ public behavior
      @   requires image != null;
      @   ensures \result != null;
      @   signals (Exception e) true; 
      @*/
    //@ skipesc
    public List<Rect> detectFaces(Mat image) {
        MatOfRect faces = new MatOfRect();
        faceDetector.detectMultiScale(image, faces, 1.1, 3, 0, new Size(30, 30), new Size());
        Rect[] facesArray = faces.toArray();
        for (Rect face : facesArray) {
            Imgproc.rectangle(image, face, new org.opencv.core.Scalar(0, 255, 0), 2);
        }
        return List.of(facesArray);
    }

    /*@ private normal_behavior
      @   requires rect != null;
      @   ensures \result == (rect.width > 50 && rect.height > 50 && rect.x >= 0 && rect.y >= 0);
      @*/
    private /*@ pure @*/ boolean isRectValid(Rect rect, Mat mat) {
        return rect.width > 50 && rect.height > 50 && rect.x >= 0 && rect.y >= 0;
    }

    /*@ public behavior
      @   requires datasetDirectory.exists();
      @   signals (Exception e) true;
      @*/
    //@ skipesc
    public void trainFaceRecognizer() {
        File[] labelDirs = datasetDirectory.listFiles(File::isDirectory);

        if (labelDirs == null) return; 

        List<Mat> images = new ArrayList<>();
        List<Integer> labels = new ArrayList<>();

        for (File labelDir : labelDirs) {
            int label;
            try {
                label = Integer.parseInt(labelDir.getName());
            } catch (NumberFormatException e) {
                continue; 
            }
            File[] imageFiles = labelDir.listFiles((dir, name) -> name.endsWith(".png"));

            if (imageFiles == null || imageFiles.length == 0) {
                System.err.println("Nenhuma imagem encontrada: " + labelDir.getAbsolutePath());
                continue;
            }

            int maxLength = String.valueOf(imageFiles.length).length();
            for (int i = 0; i < imageFiles.length; i++) {
                File oldFile = imageFiles[i];
                String newFileName = String.format("%s/%0" + maxLength + "d.png",
                        labelDir.getAbsolutePath(), i + 1);
                File newFile = new File(newFileName);
                if (!oldFile.renameTo(newFile)) System.err.println("Erro renomear: " + oldFile.getName());
            }

            imageFiles = labelDir.listFiles((dir, name) -> name.endsWith(".png"));
            if (imageFiles == null) continue;

            for (File imageFile : imageFiles) {
                Mat image = Imgcodecs.imread(imageFile.getAbsolutePath());
                if (image.empty()) continue;
                
                List<Rect> faces = detectFaces(image);

                for (Rect face : faces) {
                    if (isRectValid(face, image)) {
                        Mat faceImage = new Mat(image, face);
                        if (faceImage.rows() > 0 && faceImage.cols() > 0) {
                            Mat resizedImage = new Mat();
                            Imgproc.resize(faceImage, resizedImage, new Size(150, 150));
                            Imgproc.cvtColor(resizedImage, resizedImage, Imgproc.COLOR_BGR2GRAY);
                            images.add(resizedImage);
                            labels.add(label);
                        }
                    }
                }
            }
        }
        
        if (images.isEmpty()) return;

        LBPHFaceRecognizer faceRecognizer = LBPHFaceRecognizer.create();
        Mat labelsMat = new Mat(labels.size(), 1, CvType.CV_32SC1);
        for (int i = 0; i < labels.size(); i++) {
            labelsMat.put(i, 0, labels.get(i));
        }
        faceRecognizer.train(images, labelsMat);
        faceRecognizer.save(modelPath.toString());
    }

    //@ skipesc
    public void addNewDataToModel() {
        LBPHFaceRecognizer faceRecognizer = LBPHFaceRecognizer.create();
        faceRecognizer.read(modelPath.toString());
        faceRecognizer.save(modelPath.toString());
    }

    /*@ private behavior
      @   ensures \result != null;
      @   signals (IllegalStateException e) true;
      @*/
    private static String resolveCascadePath() {
        ClassLoader loader = ModelTrainingService.class.getClassLoader();
        
        URL resource = loader.getResource("haarcascade_frontalface_default.xml");
        
        if (resource == null) {
            throw new IllegalStateException("Não foi possível localizar o arquivo.");
        }
        try {
            return Paths.get(resource.toURI()).toFile().getAbsolutePath();
        } catch (URISyntaxException e) {
            throw new IllegalStateException("Falha ao resolver o caminho.", e);
        }
    }
}