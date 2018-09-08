imply :: (Bool, Bool) -> Bool

imply (True, False) = True
imply _ = False
