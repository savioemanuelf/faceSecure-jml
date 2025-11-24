package com.face.secure.service;

import java.io.File;
import java.util.Objects;

import com.face.secure.model.UserModel;
import com.face.secure.repositories.UserRepository;

public class UserService {

    private final UserRepository userRepository;
    private final File datasetDirectory;

    public UserService(UserRepository userRepository) {
        this(userRepository, new File("E:/dataset"));
    }

    public UserService(UserRepository userRepository, File datasetDirectory) {
        this.userRepository = Objects.requireNonNull(userRepository, "userRepository");
        this.datasetDirectory = datasetDirectory;
        if(!this.datasetDirectory.exists()) {
            this.datasetDirectory.mkdirs();
        }
    }

    public void register(UserModel userModel) {
        int label = getUnicLabel();

        userModel.setLabel(label);
        userModel.setName(userModel.getName());
        userRepository.save(userModel);

        File directory  = new File(datasetDirectory, String.valueOf(label));
        if(!directory.exists()) {
            directory.mkdirs();
        }
    }

    public int getUnicLabel() {
        File[] labelDirs  = datasetDirectory.listFiles(File::isDirectory);

        int max = 0;
        if (labelDirs != null) {
            for(File labelDir : labelDirs) {
                int label = Integer.parseInt(labelDir.getName());
                if(label > max) {
                    max = label;
                }
            }
        }
        return max + 1;
    }

    public String getNameByLabel(int label){
        return userRepository.findByLabel(label).map(UserModel::getName).orElse("Desconhecido");
    }
}
